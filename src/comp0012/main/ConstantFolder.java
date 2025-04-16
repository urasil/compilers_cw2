package comp0012.main;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Stack;
import java.util.Set;
import java.util.HashSet;
import java.util.Queue;
import java.util.LinkedList;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.ClassParser;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.*;
import org.apache.bcel.util.InstructionFinder;

public class ConstantFolder {
    ClassParser parser = null;
    ClassGen gen = null;

    JavaClass original = null;
    JavaClass optimized = null;

    boolean debug = true;
    boolean verbose = debug && false;

    public ConstantFolder(String classFilePath) {
        try {
            this.parser = new ClassParser(classFilePath);
            this.original = this.parser.parse();
            this.gen = new ClassGen(this.original);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public void optimize() {
        ConstantPoolGen cpgen = gen.getConstantPool();
        gen.setMajor(50);
        gen.setMinor(0);

        for (Method method : gen.getMethods()) {
            if (method.getCode() == null)
                continue;

            System.out.println(method.getName() + method.getSignature());

            MethodGen methodGen = new MethodGen(method, gen.getClassName(), cpgen);
            InstructionList instList = methodGen.getInstructionList();
            if (instList == null)
                continue;

            boolean modified = true;
            while (modified) {
                modified = false;

                modified |= simpleFolding(cpgen, instList);
                modified |= constantVariableFolding(cpgen, instList);
                modified |= dynamicVariableFolding(cpgen, instList);
                modified |= removeUnsedLoads(cpgen, instList);
                modified |= removeDeadCode(cpgen, instList);
                modified |= removeUselessGOTO(instList);
            }

            instList.setPositions(true);
            methodGen.setInstructionList(instList);
            methodGen.setMaxStack();
            methodGen.setMaxLocals();
            methodGen.removeLocalVariables();
            gen.replaceMethod(method, methodGen.getMethod());
        }

        optimized = gen.getJavaClass();
    }

    private boolean evaluateIntComparison(int a, int b, short opcode) {
        if (opcode == Constants.IF_ICMPEQ) {
            return (a == b);
        } else if (opcode == Constants.IF_ICMPNE) {
            return (a != b);
        } else if (opcode == Constants.IF_ICMPLT) {
            return (a < b);
        } else if (opcode == Constants.IF_ICMPLE) {
            return (a <= b);
        } else if (opcode == Constants.IF_ICMPGT) {
            return (a > b);
        } else if (opcode == Constants.IF_ICMPGE) {
            return (a >= b);
        } else {
            throw new UnsupportedOperationException("Unknown comparison opcode: " + opcode);
        }
    }

    private boolean checkBranchCondition(int cmpResult, short opcode) {
        if (opcode == Constants.IFLE) {
            return cmpResult <= 0;
        } else if (opcode == Constants.IFLT) {
            return cmpResult < 0;
        } else if (opcode == Constants.IFGE) {
            return cmpResult >= 0;
        } else if (opcode == Constants.IFGT) {
            return cmpResult > 0;
        } else if (opcode == Constants.IFEQ) {
            return cmpResult == 0;
        } else if (opcode == Constants.IFNE) {
            return cmpResult != 0;
        } else {
            throw new UnsupportedOperationException("Unknown comparison opcode: " + opcode);
        }
    }

    private boolean isConstantPushInstruction(Instruction inst) {
        // checks if instruction pushes a constant value onto stack
        return (inst instanceof LDC) ||
                (inst instanceof LDC2_W) ||
                (inst instanceof BIPUSH) ||
                (inst instanceof SIPUSH) ||
                (inst instanceof ICONST) ||
                (inst instanceof FCONST) ||
                (inst instanceof LCONST) ||
                (inst instanceof DCONST);
    }

    private void updateLostTargetReferences(TargetLostException e, InstructionHandle newTarget) {
        InstructionHandle[] lostTargets = e.getTargets();
        for (InstructionHandle lost : lostTargets) {
            InstructionTargeter[] targeters = lost.getTargeters();
            if (targeters != null) {
                for (InstructionTargeter t : targeters) {
                    t.updateTarget(lost, newTarget);
                }
            }
        }
    }

    private Number getConstantValue(Instruction inst, ConstantPoolGen cpg) {
        if (inst instanceof LDC) {
            Object value = ((LDC) inst).getValue(cpg);
            if (value instanceof Number) {
                return (Number) value;
            }
        } else if (inst instanceof LDC2_W) {
            Object value = ((LDC2_W) inst).getValue(cpg);
            if (value instanceof Number) {
                return (Number) value;
            }
        } else if (inst instanceof BIPUSH) {
            return ((BIPUSH) inst).getValue();
        } else if (inst instanceof SIPUSH) {
            return ((SIPUSH) inst).getValue();
        } else if (inst instanceof ICONST) {
            return ((ICONST) inst).getValue();
        } else if (inst instanceof FCONST) {
            return ((FCONST) inst).getValue();
        } else if (inst instanceof LCONST) {
            return ((LCONST) inst).getValue();
        } else if (inst instanceof DCONST) {
            return ((DCONST) inst).getValue();
        }
        return null;
    }

    private Instruction createConstantInstruction(Number value, ConstantPoolGen cpg) {
        if (value instanceof Integer) {
            int val = value.intValue();
            if (val >= -1 && val <= 5) {
                return new ICONST(val);
            } else if (val >= Byte.MIN_VALUE && val <= Byte.MAX_VALUE) {
                return new BIPUSH((byte) val);
            } else if (val >= Short.MIN_VALUE && val <= Short.MAX_VALUE) {
                return new SIPUSH((short) val);
            } else {
                return new LDC(cpg.addInteger(val));
            }
        } else if (value instanceof Long) {
            long val = value.longValue();
            if (val == 0L || val == 1L) {
                return new LCONST((int) val);
            } else {
                return new LDC2_W(cpg.addLong(val));
            }
        } else if (value instanceof Float) {
            float val = value.floatValue();
            if (val == 0.0f || val == 1.0f || val == 2.0f) {
                return new FCONST(val);
            } else {
                return new LDC(cpg.addFloat(val));
            }
        } else if (value instanceof Double) {
            double val = value.doubleValue();
            if (val == 0.0 || val == 1.0) {
                return new DCONST(val);
            } else {
                return new LDC2_W(cpg.addDouble(val));
            }
        }
        throw new UnsupportedOperationException("Unsupported value type: " + value.getClass().getName());
    }

    private Number executeArithmeticOperation(Number val1, Number val2, Instruction arithmeticInst) {
        String opName = arithmeticInst.getName().toUpperCase();

        if (opName.startsWith("I")) {
            int a = val1.intValue();
            int b = val2.intValue();

            if ("IADD".equals(opName)) {
                return a + b;
            } else if ("ISUB".equals(opName)) {
                return a - b;
            } else if ("IMUL".equals(opName)) {
                return a * b;
            } else if ("IDIV".equals(opName)) {
                if (b == 0) {
                    throw new ArithmeticException("Division by zero");
                }
                return a / b;
            } else if ("IREM".equals(opName)) {
                if (b == 0) {
                    throw new ArithmeticException("Division by zero");
                }
                return a % b;
            }
        }

        if (opName.startsWith("L")) {
            long a = val1.longValue();
            long b = val2.longValue();

            if ("LADD".equals(opName)) {
                return a + b;
            } else if ("LSUB".equals(opName)) {
                return a - b;
            } else if ("LMUL".equals(opName)) {
                return a * b;
            } else if ("LDIV".equals(opName)) {
                if (b == 0) {
                    throw new ArithmeticException("Division by zero");
                }
                return a / b;
            } else if ("LREM".equals(opName)) {
                if (b == 0) {
                    throw new ArithmeticException("Division by zero");
                }
                return a % b;
            }
        }

        if (opName.startsWith("F")) {
            float a = val1.floatValue();
            float b = val2.floatValue();

            if ("FADD".equals(opName)) {
                return a + b;
            } else if ("FSUB".equals(opName)) {
                return a - b;
            } else if ("FMUL".equals(opName)) {
                return a * b;
            } else if ("FDIV".equals(opName)) {
                return a / b;
            } else if ("FREM".equals(opName)) {
                return a % b;
            }
        }

        if (opName.startsWith("D")) {
            double a = val1.doubleValue();
            double b = val2.doubleValue();

            if ("DADD".equals(opName)) {
                return a + b;
            } else if ("DSUB".equals(opName)) {
                return a - b;
            } else if ("DMUL".equals(opName)) {
                return a * b;
            } else if ("DDIV".equals(opName)) {
                return a / b;
            } else if ("DREM".equals(opName)) {
                return a % b;
            }
        }

        return null;
    }

    private boolean simpleFolding(ConstantPoolGen cpgen, InstructionList instructionList) {
        boolean modified = false;

        InstructionFinder finder = new InstructionFinder(instructionList);
        String pattern = "PushInstruction (ConversionInstruction)? PushInstruction (ConversionInstruction)? ArithmeticInstruction";

        for (Iterator it = finder.search(pattern); it.hasNext();) {
            int push1Pos = 0;
            int push2Pos = 1;
            int arithmeticPos;
        
            InstructionHandle[] set = (InstructionHandle[]) it.next();

            if (set[1].getInstruction() instanceof ConversionInstruction) {
                push2Pos = 2;
            }
            if(set[push2Pos+1].getInstruction() instanceof ConversionInstruction) {
                arithmeticPos = push2Pos + 2;
            }else{
                arithmeticPos = push2Pos + 1;
            }

            Instruction push1 = set[push1Pos].getInstruction();
            Instruction push2 = set[push2Pos].getInstruction();
            Instruction arithmeticInst = set[arithmeticPos].getInstruction();
    

            Number val1 = getConstantValue(push1, cpgen);
            Number val2 = getConstantValue(push2, cpgen);

            if (val1 == null || val2 == null) {
                continue;
            }

            Number res = executeArithmeticOperation(val1, val2, arithmeticInst);
            if (res != null) {
                Instruction r = createConstantInstruction(res, cpgen);
                
                InstructionHandle newHandle = instructionList.insert(set[0], r);

                for (int i = 0; i < set.length; i++) {
                    safeDelete(instructionList, set[i], newHandle);
                }

                modified = true;
            }
        }

        return modified;
    }

    private void safeDelete(InstructionList l, InstructionHandle handle, InstructionHandle newTarget) {
        try {
            if (debug) {
                System.out.println("Deleting: " + handle);
            }
            l.delete(handle);
        } catch (TargetLostException e) { // if a GOTO / cjumps to the deleted instruction
            if (debug) {
                System.out.println("Target lost: " + handle + " -> " + newTarget);
            }
            for (InstructionHandle branchingInstruction : e.getTargets()) {
                for (InstructionTargeter targeter : branchingInstruction.getTargeters())
                    targeter.updateTarget(branchingInstruction, newTarget);
            }
        }
    }

    private boolean constantVariableFolding(ConstantPoolGen cpgen, InstructionList instList) {
        boolean modified = false;

        HashMap<Integer, Boolean> constantVars = new HashMap<>();
        HashMap<Integer, Number> literalValues = new HashMap<>();

        // first pass-> mark variables assigned via IINC or multiple stores as
        // non-constant
        for (InstructionHandle handle : instList.getInstructionHandles()) {
            Instruction inst = handle.getInstruction();
            if (inst instanceof IINC) {
                int idx = ((IINC) inst).getIndex();
                constantVars.put(idx, false);
            } else if (inst instanceof StoreInstruction) {
                int idx = ((StoreInstruction) inst).getIndex();
                if (!constantVars.containsKey(idx))
                    constantVars.put(idx, true);
                else
                    constantVars.put(idx, false);

            }
        }

        // second pass-> record literal constant values from push + store patterns
        String pattern = "(LDC | LDC2_W | ConstantPushInstruction) (DSTORE | FSTORE | ISTORE | LSTORE)";
        InstructionFinder finder = new InstructionFinder(instList);
        for (Iterator it = finder.search(pattern); it.hasNext();) {
            InstructionHandle[] set = (InstructionHandle[]) it.next();
            PushInstruction push = (PushInstruction) set[0].getInstruction();
            StoreInstruction store = (StoreInstruction) set[1].getInstruction();
            int idx = store.getIndex();
            if (constantVars.containsKey(idx) && constantVars.get(idx)) {
                Number val = getConstantValue((Instruction) push, cpgen);
                if (val == null)
                    System.err.println("FATAL: Could not obtain literal value for unknown type");
                else
                    literalValues.put(idx, val);
            }
        }

        // third pass-> replace load instructions with constant push instructions.
        String loadPattern = "(DLOAD | FLOAD | ILOAD | LLOAD)";
        for (Iterator it = finder.search(loadPattern); it.hasNext();) {
            InstructionHandle[] set = (InstructionHandle[]) it.next();
            LoadInstruction load = (LoadInstruction) set[0].getInstruction();
            int idx = load.getIndex();
            if (literalValues.containsKey(idx)) {
                Instruction added = null;
                Number val = literalValues.get(idx);
                if (load.getType(cpgen).equals(Type.FLOAT))
                    added = new LDC(cpgen.addFloat(val.floatValue()));
                else if (load.getType(cpgen).equals(Type.DOUBLE))
                    added = new LDC2_W(cpgen.addDouble(val.doubleValue()));
                else if (load.getType(cpgen).equals(Type.LONG))
                    added = new LDC2_W(cpgen.addLong(val.longValue()));
                else if (load.getType(cpgen).equals(Type.INT))
                    added = new LDC(cpgen.addInteger(val.intValue()));

                modified = true;
                assert added != null;
                InstructionHandle newHandle = instList.insert(set[0], added);
                safeDelete(instList, set[0], newHandle);
                
            }
        }

        // fourth pass-> find comparison patterns where both operands are constants
        String comparisonPattern = "(LDC | LDC2_W | ConstantPushInstruction) (LDC | LDC2_W | ConstantPushInstruction) (IF_ICMPLT | IF_ICMPGT | IF_ICMPLE | IF_ICMPGE | IF_ICMPEQ | IF_ICMPNE)";
        for (Iterator it = finder.search(comparisonPattern); it.hasNext();) {
            InstructionHandle[] set = (InstructionHandle[]) it.next();
            Number val1 = getConstantValue(set[0].getInstruction(), cpgen);
            Number val2 = getConstantValue(set[1].getInstruction(), cpgen);
            IfInstruction ifInst = (IfInstruction) set[2].getInstruction();

            if (val1 != null && val2 != null) {
                boolean result = evaluateIntComparison(val1.intValue(), val2.intValue(), ifInst.getOpcode());

                InstructionHandle newHandle = set[0].getPrev();
                if (result) {
                    BranchInstruction newInst = new GOTO(ifInst.getTarget());
                    newHandle = instList.insert(set[0], newInst);
                    if (debug) {
                        System.out.println("Folding: " + set[0].getInstruction() + " (" + val1 + ")" + " "
                                + set[1].getInstruction() + " (" + val2 + ")" + " " + ifInst.getName() + " => "
                                + newInst);
                    }
                }

                safeDelete(instList, set[0], newHandle);
                safeDelete(instList, set[1], newHandle);
                safeDelete(instList, set[2], newHandle);

                modified = true;

            }
        }

        // Also handle long comparisons
        String longCompPattern = "(LDC2_W) (LDC2_W) LCMP (IFLT | IFGT | IFLE | IFGE | IFEQ | IFNE)";
        for (Iterator it = finder.search(longCompPattern); it.hasNext();) {
            InstructionHandle[] set = (InstructionHandle[]) it.next();
            Number val1 = getConstantValue(set[0].getInstruction(), cpgen);
            Number val2 = getConstantValue(set[1].getInstruction(), cpgen);

            if (val1 != null && val2 != null) {
                int cmpResult = Long.compare(val1.longValue(), val2.longValue());
                IfInstruction ifInst = (IfInstruction) set[3].getInstruction();
                boolean branch = checkBranchCondition(cmpResult, ifInst.getOpcode());

                // Replace with GOTO 
                InstructionHandle newHandle = set[0].getPrev();
                if (branch) {
                    BranchInstruction newInst = new GOTO(ifInst.getTarget());
                    newHandle = instList.insert(set[0], newInst);

                    if (debug) {
                        System.out.println("Folding: " + set[0].getInstruction() + " (" + val1 + ")" + " "
                                + set[1].getInstruction() + " (" + val2 + ")" + " LCMP " + ifInst.getName() + " => "
                                + newInst);
                        System.out.println("Adding: " + newInst);
                    }
                }

                safeDelete(instList, set[0], newHandle);
                safeDelete(instList, set[1], newHandle);
                safeDelete(instList, set[2], newHandle);
                safeDelete(instList, set[3], newHandle);

                modified = true;

            }
        }
	// is this really necessary?
        // fifth pass-> find and replace return statements with constant expressions
        String returnPattern = "IRETURN";
        for (Iterator it = finder.search(returnPattern); it.hasNext();) {
            InstructionHandle[] set = (InstructionHandle[]) it.next();
            InstructionHandle returnHandle = set[0];
            InstructionHandle current = returnHandle.getPrev();

            // pushing bool value
            if (current != null && current.getInstruction() instanceof ICONST &&
                    ((ICONST) current.getInstruction()).getValue().intValue() == 1) {

                //instructions to delete
                List<InstructionHandle> toDelete = new ArrayList<>();
                InstructionHandle prev = current.getPrev();

                // look backward through the instruction list for any constant pushes
                while (prev != null) {
                    Instruction inst = prev.getInstruction();
                    InstructionHandle prevPrev = prev.getPrev();

                    // if we find a store instruction, we need to also find its source
                    if (inst instanceof StoreInstruction) {
                        toDelete.add(prev);
                        if (prevPrev != null && isConstantPushInstruction(prevPrev.getInstruction())) {
                            toDelete.add(prevPrev);
                            prev = prevPrev.getPrev();
                        } else {
                            prev = prevPrev;
                        }
                    }
                    else if (isConstantPushInstruction(inst)) {
                        toDelete.add(prev);
                        prev = prevPrev;
                    }
                    else {
                        break;
                    }
                }

                // delete all the unused inst
                if (!toDelete.isEmpty()) {
                    for (InstructionHandle h : toDelete) {
                        safeDelete(instList, h, current);
                    }
                    modified = true;
                }
            }
        }

        return modified;
    }

    private boolean dynamicVariableFolding(ConstantPoolGen cpgen, InstructionList instList) {
        boolean optimizationApplied = false;
        int slotCounter = 0;
        for (InstructionHandle h = instList.getStart(); h != null; h = h.getNext()) {
            Instruction inst = h.getInstruction();
            if (inst instanceof LocalVariableInstruction) {
                int idx = ((LocalVariableInstruction) inst).getIndex();
                if (idx >= slotCounter) {
                    slotCounter = idx + 1; // +1 because indices are 0-based
                }
            } else if (inst instanceof IINC) {
                int idx = ((IINC) inst).getIndex();
                if (idx >= slotCounter) {
                    slotCounter = idx + 1;
                }
            }
        }

        // mapping from original variable indices to their versioned indices
        Map<Integer, Integer> slotMapping = new HashMap<>();
        List<int[]> loopBoundaryPositions = new ArrayList<>();
        List<int[]> branchBoundaryPositions = new ArrayList<>();

        for (InstructionHandle h = instList.getStart(); h != null; h = h.getNext()) {
            if (h.getInstruction() instanceof BranchInstruction) {
                InstructionHandle dest = ((BranchInstruction) h.getInstruction()).getTarget();
                // if target position is earlier than current position -> loop
                if (dest.getPosition() < h.getPosition()) {
                    int[] loopRegion = {dest.getPosition(), h.getPosition()};
                    loopBoundaryPositions.add(loopRegion);
                    if (debug) {
                        System.out.println("Loop found: " + dest.getPosition() + "-" + h.getPosition());
                    }
                }
            }
        }

        // sdcan for branches (if statements that aren't GOTOs)
        for (InstructionHandle h = instList.getStart(); h != null; h = h.getNext()) {
            if (h.getInstruction() instanceof IfInstruction &&
                !(h.getInstruction() instanceof GOTO)) {
                InstructionHandle target = ((IfInstruction) h.getInstruction()).getTarget();
                if (h.getNext() != null && target.getPrev() != null) {
                    int[] branchRegion = {h.getNext().getPosition(), target.getPrev().getPosition()};
                    branchBoundaryPositions.add(branchRegion);
                    if (debug) {
                        System.out.println("Branch found: " + h.getNext().getPosition() +
                                        "-" + target.getPrev().getPosition());
                    }
                }
            }
        }

        for (InstructionHandle currentInst = instList.getStart(); currentInst != null;) {
            InstructionHandle nextInst = currentInst.getNext();
            Instruction instruction = currentInst.getInstruction();
            int currentPosition = currentInst.getPosition();

            // STORE instructions - creating new versions
            if (instruction instanceof StoreInstruction) {
                int originalSlot = ((StoreInstruction) instruction).getIndex();

                // Safety check: is this variable modified in a loop or branch?
                boolean isUnsafe = false;

                for (int[] loopRegion : loopBoundaryPositions) {
                    if (currentPosition >= loopRegion[0] && currentPosition <= loopRegion[1]) {
                        for (InstructionHandle scanInst = instList.getStart();
                            scanInst != null;
                            scanInst = scanInst.getNext()) {

                            int scanPosition = scanInst.getPosition();
                            if (scanPosition >= loopRegion[0] && scanPosition <= loopRegion[1]) {
                                Instruction scanInstruction = scanInst.getInstruction();
                                // check if this instruction modifies our variable
                                if ((scanInstruction instanceof StoreInstruction &&
                                    ((StoreInstruction) scanInstruction).getIndex() == originalSlot) ||
                                    (scanInstruction instanceof IINC &&
                                    ((IINC) scanInstruction).getIndex() == originalSlot)) {
                                    isUnsafe = true;
                                    break;
                                }
                            }
                        }
                        if (isUnsafe) break;
                    }
                }

                if (!isUnsafe) {
                    for (int[] branchRegion : branchBoundaryPositions) {
                        // is within this branch
                        if (currentPosition >= branchRegion[0] && currentPosition <= branchRegion[1]) {
                            for (InstructionHandle scanInst = instList.getStart();
                                scanInst != null;
                                scanInst = scanInst.getNext()) {

                                int scanPosition = scanInst.getPosition();
                                if (scanPosition >= branchRegion[0] && scanPosition <= branchRegion[1]) {
                                    Instruction scanInstruction = scanInst.getInstruction();
				    //again check if this instruction modifies our variable
                                    if ((scanInstruction instanceof StoreInstruction &&
                                        ((StoreInstruction) scanInstruction).getIndex() == originalSlot) ||
                                        (scanInstruction instanceof IINC &&
                                        ((IINC) scanInstruction).getIndex() == originalSlot)) {
                                        isUnsafe = true;
                                        break;
                                    }
                                }
                            }
                            if (isUnsafe) break;
                        }
                    }
                }

                if (!isUnsafe) {
                    int newSlot;
                    if (slotMapping.containsKey(originalSlot)) {
                        newSlot = slotCounter++;
                        optimizationApplied = true;

                        if (debug) {
                            System.out.println("Versioning variable " + originalSlot +
                                            " to new slot " + newSlot +
                                            " at position " + currentPosition);
                        }
                    } else {
                        newSlot = originalSlot;
                    }

                    slotMapping.put(originalSlot, newSlot);
                    ((StoreInstruction) instruction).setIndex(newSlot);
                }
            }
            // LOAD instructions - update to use the correct version
            else if (instruction instanceof LoadInstruction) {
                int originalSlot = ((LoadInstruction) instruction).getIndex();

                // if we have a mapping for this variable, update the load
                if (slotMapping.containsKey(originalSlot)) {
                    int mappedSlot = slotMapping.get(originalSlot);
                    ((LoadInstruction) instruction).setIndex(mappedSlot);

                    if (debug && mappedSlot != originalSlot) {
                        System.out.println("Updated LOAD from slot " + originalSlot +
                                        " to " + mappedSlot +
                                        " at position " + currentPosition);
                    }
                }
            }

            currentInst = nextInst;
        }

        return optimizationApplied;
    }

    private boolean removeUselessGOTO(InstructionList instList) {
        boolean modified = false;
        InstructionHandle[] handles = instList.getInstructionHandles();

        for (int i = 0; i < handles.length; i++) {
            InstructionHandle handle = handles[i];
            Instruction inst = handle.getInstruction();
            if (inst instanceof GOTO) {
                GOTO g = (GOTO) inst;
                InstructionHandle target = g.getTarget();
                // remove this goto if it points to next instruction anyways
                if (target.getPosition() == handle.getNext().getPosition()) {
                    safeDelete(instList, handle, handle.getNext());
                    modified = true;
                    
                }

            }
        }
        return modified;
    }

    private boolean removeDeadCode(ConstantPoolGen cpgen, InstructionList instList) {
        boolean modified = false;
        InstructionHandle[] handles = instList.getInstructionHandles();

        Set<InstructionHandle> alive = new HashSet<>();
        Queue<InstructionHandle> toProcess = new LinkedList<>();

        // STart
        if (handles.length > 0) {
            toProcess.add(handles[0]);
        }

        // BFS
        while (!toProcess.isEmpty()) {
            InstructionHandle current = toProcess.poll();

            if (alive.contains(current)) {
                continue;
            }

            alive.add(current);
            Instruction inst = current.getInstruction();

            // Handle regular flow
            if (!(inst instanceof BranchInstruction) || inst instanceof ReturnInstruction) {
                if (current.getNext() != null) {
                    toProcess.add(current.getNext());
                }
            }

            // Handle jumps
            if (inst instanceof BranchInstruction) {
                BranchInstruction branch = (BranchInstruction) inst;
                toProcess.add(branch.getTarget());

                // cjumps
                if (inst instanceof IfInstruction && !(inst instanceof GOTO)) {
                    if (current.getNext() != null) {
                        toProcess.add(current.getNext());
                    }
                }
            }
        }

        InstructionHandle current = instList.getStart();
        while (current != null) {
            InstructionHandle next = current.getNext();
            if (!alive.contains(current)) {
                safeDelete(instList, current, current.getPrev());
                modified = true;
            }
            current = next;
        }

        return modified;
    }

    private boolean removeUnsedLoads(ConstantPoolGen cpgen, InstructionList instList) {
        boolean modified = false;

        // gather loads and stores by index
        Map<Integer, List<InstructionHandle>> loadsByVar = new HashMap<>();
        Map<Integer, List<InstructionHandle>> storesByVar = new HashMap<>();

        for (InstructionHandle ih : instList.getInstructionHandles()) {
            Instruction inst = ih.getInstruction();
            if (inst instanceof LoadInstruction) {
                int idx = ((LoadInstruction) inst).getIndex();
                loadsByVar.computeIfAbsent(idx, k -> new ArrayList<>()).add(ih);
            } else if (inst instanceof StoreInstruction) {
                int idx = ((StoreInstruction) inst).getIndex();
                storesByVar.computeIfAbsent(idx, k -> new ArrayList<>()).add(ih);
            }
        }

        if (verbose) {
            System.out.println("Load instructions: " + loadsByVar);
            System.out.println("Store instructions: " + storesByVar);
        }

        // check if each store is used before the next store overwrites it
        for (Map.Entry<Integer, List<InstructionHandle>> entry : storesByVar.entrySet()) {
            int varIndex = entry.getKey();
            List<InstructionHandle> storeHandles = entry.getValue();
            List<InstructionHandle> loadHandles = loadsByVar.getOrDefault(varIndex, new ArrayList<>());

            // process them in linear order
            storeHandles.sort(Comparator.comparingInt(h -> h.getPosition()));
            loadHandles.sort(Comparator.comparingInt(h -> h.getPosition()));

            for (int i = 0; i < storeHandles.size(); i++) {
                InstructionHandle storeIH = storeHandles.get(i);
                int storePos = storeIH.getPosition();

                // next store overwrites variable
                InstructionHandle nextStoreIH = (i + 1 < storeHandles.size()) ? storeHandles.get(i + 1) : null;
                int nextStorePos = (nextStoreIH == null) ? Integer.MAX_VALUE : nextStoreIH.getPosition();

                // check for load between storePos and nextStorePos
                boolean used = false;
                for (InstructionHandle loadIH : loadHandles) {
                    int loadPos = loadIH.getPosition();
                    if (loadPos > storePos && loadPos < nextStorePos) {
                        used = true;
                        break;
                    }
                }

                // remove this store
                if (!used) {
                    try {
                        // remove a constant push right before the store if it only served this store
                        InstructionHandle prev = storeIH.getPrev();
                        if (prev != null && isConstantPushInstruction(prev.getInstruction())) {
                            instList.delete(prev);
                        }
                        instList.delete(storeIH);
                        modified = true;
                    } catch (TargetLostException e) {
                        updateLostTargetReferences(e, storeIH.getNext());
                    }
                }
            }
        }

        return modified;
    }

    public void write(String optimisedFilePath) {
        this.optimize();

        try {
            FileOutputStream out = new FileOutputStream(new File(optimisedFilePath));
            this.optimized.dump(out);
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
