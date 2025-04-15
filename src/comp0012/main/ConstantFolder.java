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

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.ClassParser;
import org.apache.bcel.classfile.Constant;
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
                modified |= removeUnreachableCode(cpgen, instList);
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

    // UTILITY FUNCTIONS
    // long comparisons
    private boolean evaluateComparison(int cmpResult, short opcode) {
        switch (opcode) {
            case Constants.IFLE:
                return cmpResult <= 0;
            case Constants.IFLT:
                return cmpResult < 0;
            case Constants.IFGE:
                return cmpResult >= 0;
            case Constants.IFGT:
                return cmpResult > 0;
            case Constants.IFEQ:
                return cmpResult == 0;
            case Constants.IFNE:
                return cmpResult != 0;
            default:
                throw new UnsupportedOperationException("Unknown comparison opcode: " + opcode);
        }
    }

    // int comparisons
    private boolean isIntComparison(short opcode) {
        switch (opcode) {
            case Constants.IF_ICMPEQ:
            case Constants.IF_ICMPNE:
            case Constants.IF_ICMPLT:
            case Constants.IF_ICMPLE:
            case Constants.IF_ICMPGT:
            case Constants.IF_ICMPGE:
                return true;
            default:
                return false;
        }
    }

    private boolean evaluateIntComparison(int a, int b, short opcode) {
        switch (opcode) {
            case Constants.IF_ICMPEQ:
                return (a == b);
            case Constants.IF_ICMPNE:
                return (a != b);
            case Constants.IF_ICMPLT:
                return (a < b);
            case Constants.IF_ICMPLE:
                return (a <= b);
            case Constants.IF_ICMPGT:
                return (a > b);
            case Constants.IF_ICMPGE:
                return (a >= b);
            default:
                throw new UnsupportedOperationException("Unknown comparison opcode: " + opcode);
        }
    }

    private void handleTargetLost(TargetLostException e, InstructionHandle newTarget) {
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

    // check for conversion instr instances
    private boolean isConversionInstruction(Instruction inst) {
        return inst instanceof ConversionInstruction;
    }

    // do i2l, etc
    private Number performConversion(Number value, Instruction convInst) {
        String opName = convInst.getName().toUpperCase();

        switch (opName) {
            case "I2L":
                return value.longValue();
            case "I2F":
                return value.floatValue();
            case "I2D":
                return value.doubleValue();
            case "L2I":
                return value.intValue();
            case "L2F":
                return value.floatValue();
            case "L2D":
                return value.doubleValue();
            case "F2I":
                return (int) value.floatValue();
            case "F2L":
                return (long) value.floatValue();
            case "F2D":
                return value.doubleValue();
            case "D2I":
                return (int) value.doubleValue();
            case "D2L":
                return (long) value.doubleValue();
            case "D2F":
                return (float) value.doubleValue();
            default:
                return null;
        }
    }

    // checks if the instruction pushes a constant value to the stack
    private boolean isConstantPushInstruction(Instruction inst) {
        return (inst instanceof LDC) ||
                (inst instanceof LDC2_W) ||
                (inst instanceof BIPUSH) ||
                (inst instanceof SIPUSH) ||
                (inst instanceof ICONST) ||
                (inst instanceof FCONST) ||
                (inst instanceof LCONST) ||
                (inst instanceof DCONST);
    }

    // checks if arithmetic operation
    private boolean isArithmeticInstruction(Instruction inst) {
        return (inst instanceof ArithmeticInstruction);
    }

    // gets constant value from instruction.
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

    // redirects targets from old instruction to the new one
    private void redirectTargets(InstructionHandle h1, InstructionHandle h2,
            InstructionHandle h3, InstructionHandle newHandle) {
        if (h1.hasTargeters()) {
            InstructionTargeter[] targeters = h1.getTargeters();
            for (InstructionTargeter targeter : targeters) {
                targeter.updateTarget(h1, newHandle);
            }
        }

        if (h2.hasTargeters()) {
            InstructionTargeter[] targeters = h2.getTargeters();
            for (InstructionTargeter targeter : targeters) {
                targeter.updateTarget(h2, newHandle);
            }
        }

        if (h3.hasTargeters()) {
            InstructionTargeter[] targeters = h3.getTargeters();
            for (InstructionTargeter targeter : targeters) {
                targeter.updateTarget(h3, newHandle);
            }
        }
    }

    // computes operation
    private Number computeArithmeticResult(Number val1, Number val2, Instruction arithmeticInst) {
        String opName = arithmeticInst.getName().toUpperCase();

        // int
        if (opName.startsWith("I")) {
            int a = val1.intValue();
            int b = val2.intValue();

            switch (opName) {
                case "IADD":
                    return a + b;
                case "ISUB":
                    return a - b;
                case "IMUL":
                    return a * b;
                case "IDIV":
                    if (b == 0)
                        throw new ArithmeticException("Division by zero");
                    return a / b;
                case "IREM":
                    if (b == 0)
                        throw new ArithmeticException("Division by zero");
                    return a % b;
            }
        }

        // long
        if (opName.startsWith("L")) {
            long a = val1.longValue();
            long b = val2.longValue();

            switch (opName) {
                case "LADD":
                    return a + b;
                case "LSUB":
                    return a - b;
                case "LMUL":
                    return a * b;
                case "LDIV":
                    if (b == 0)
                        throw new ArithmeticException("Division by zero");
                    return a / b;
                case "LREM":
                    if (b == 0)
                        throw new ArithmeticException("Division by zero");
                    return a % b;
            }
        }

        // float
        if (opName.startsWith("F")) {
            float a = val1.floatValue();
            float b = val2.floatValue();

            switch (opName) {
                case "FADD":
                    return a + b;
                case "FSUB":
                    return a - b;
                case "FMUL":
                    return a * b;
                case "FDIV":
                    return a / b;
                case "FREM":
                    return a % b;
            }
        }

        // double
        if (opName.startsWith("D")) {
            double a = val1.doubleValue();
            double b = val2.doubleValue();

            switch (opName) {
                case "DADD":
                    return a + b;
                case "DSUB":
                    return a - b;
                case "DMUL":
                    return a * b;
                case "DDIV":
                    return a / b;
                case "DREM":
                    return a % b;
            }
        }

        return null;
    }

    // creates constant-pushing instruction for numeric value.
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

    // PERFORM SIMPLE FOLDING
    private boolean simpleFolding(ConstantPoolGen cpgen, InstructionList instructionList) {
        boolean modified = false;

        InstructionFinder finder = new InstructionFinder(instructionList);
        String pattern = "PushInstruction PushInstruction (ConversionInstruction)? ArithmeticInstruction";

        for (Iterator it = finder.search(pattern); it.hasNext();) {
            
            InstructionHandle[] set = (InstructionHandle[]) it.next();
            
            Instruction inst1 = set[0].getInstruction();
            Instruction inst2 = set[1].getInstruction();
            Instruction inst3 = set[2].getInstruction();
            Instruction arithmeticInst = inst3;
            
            if (set.length == 4) {
                arithmeticInst = set[3].getInstruction();
            }

            Number val1 = getConstantValue(inst1, cpgen);
            Number val2 = getConstantValue(inst2, cpgen);

            if (val1 == null || val2 == null) {
                continue;
            }

            Number res = computeArithmeticResult(val1, val2, arithmeticInst);
            if (res != null) {
                Instruction r = createConstantInstruction(res, cpgen);
                if(debug){
                    if(set.length == 4){
                        System.out.println("Folding: " + inst1 + " ("+val1+")"+" " + inst2 + " ("+val2+")" + " "+ inst3 + " "+ arithmeticInst.getName() + " => " + r);
                    }else{
                        System.out.println("Folding: " + inst1 + " ("+val1+")"+" " + inst2 + " ("+val2+")" + " "+ arithmeticInst.getName() + " => " + r);
                    }
                }

                instructionList.insert(set[0], r);

                safeDelete(instructionList, set[0], set[0].getPrev());
                safeDelete(instructionList, set[1], set[0].getPrev());
                safeDelete(instructionList, set[2], set[0].getPrev());
                if (set.length == 4) {
                    safeDelete(instructionList, set[3], set[0].getPrev());
                }

                modified = true;
            }
        }

        return modified;
    }

    private void safeDelete(InstructionList l, InstructionHandle handle, InstructionHandle newTarget) {
        try {
            if(debug){
                System.out.println("Deleting: " + handle);
            }
            l.delete(handle);
        } catch (TargetLostException e) { // if a GOTO / cjumps to the deleted instruction
            if(debug){
                System.out.println("Target lost: " + handle + " -> " + newTarget);
            }
            for (InstructionHandle branchingInstruction : e.getTargets()) {
                for (InstructionTargeter targeter : branchingInstruction.getTargeters())
                    targeter.updateTarget(branchingInstruction, newTarget);
            }
        }
    }

    private void applyConversion(Instruction inst, Stack<Number> valueStack, Stack<InstructionHandle> handleStack) {
        if (!valueStack.isEmpty()) {
            Number value = valueStack.pop();
            InstructionHandle handle = handleStack.pop();
            Number converted = performConversion(value, inst);
            if (converted != null) {
                valueStack.push(converted);
                handleStack.push(handle);
            }
        }
    }

    private boolean foldArithmetic(Instruction inst, ConstantPoolGen cpgen, InstructionList list,
            Stack<Number> valueStack, Stack<InstructionHandle> handleStack,
            InstructionHandle current) {
        if (valueStack.size() < 2)
            return false;

        Number b = valueStack.pop(), a = valueStack.pop();
        InstructionHandle hb = handleStack.pop(), ha = handleStack.pop();
        Number result = computeArithmeticResult(a, b, inst);

        if (result != null) {
            Instruction newInst = createConstantInstruction(result, cpgen);
            InstructionHandle newHandle = list.insert(ha, newInst);
            redirectTargets(ha, hb, current, newHandle);
            try {
                list.delete(ha, current);
            } catch (TargetLostException e) {
                handleTargetLost(e, newHandle);
            }
            return true;
        }

        return false;
    }

    private boolean foldFloatingComparison(Instruction inst, ConstantPoolGen cpgen, InstructionList list,
            Stack<Number> valueStack, Stack<InstructionHandle> handleStack,
            InstructionHandle current) {
        if (valueStack.size() < 2 || current.getNext() == null)
            return false;

        Number b = valueStack.pop(), a = valueStack.pop();
        InstructionHandle hb = handleStack.pop(), ha = handleStack.pop();
        InstructionHandle next = current.getNext();
        Instruction nextInst = next.getInstruction();

        if (!(nextInst instanceof IfInstruction))
            return false;

        short opcode = ((IfInstruction) nextInst).getOpcode();
        boolean result = evaluateFloatingComparison(inst, a, b);
        boolean branch = evaluateComparison(result ? 1 : 0, opcode);

        InstructionHandle target = ((IfInstruction) nextInst).getTarget();
        
        Instruction newInst = branch ? new GOTO(target) : new NOP();
        InstructionHandle newHandle = list.insert(ha, newInst);

        redirectTargets(ha, hb, current, newHandle);
        updateTargeters(next, branch ? target : newHandle);

        try {
            if (branch)
                list.delete(ha, next);
            else
                list.delete(ha.getNext(), next);
        } catch (TargetLostException e) {
            handleTargetLost(e, branch ? target : next.getNext());
        }

        return true;
    }

    private boolean foldIntComparison(IfInstruction inst, ConstantPoolGen cpgen, InstructionList list,
            Stack<Number> valueStack, Stack<InstructionHandle> handleStack,
            InstructionHandle current) {
        if (valueStack.size() < 2)
            return false;

        Number b = valueStack.pop(), a = valueStack.pop();
        InstructionHandle hb = handleStack.pop(), ha = handleStack.pop();
        boolean result = evaluateIntComparison(a.intValue(), b.intValue(), inst.getOpcode());
        InstructionHandle newHandle;

        if (result) {
            GOTO gotoInst = new GOTO(inst.getTarget());
            newHandle = list.insert(ha, gotoInst);
        } else {
            newHandle = current.getNext();
        }

        redirectTargets(ha, hb, current, newHandle);

        try {
            list.delete(ha, current);
        } catch (TargetLostException e) {
            handleTargetLost(e, newHandle);
        }

        return true;
    }

    private boolean isFloatingPointComparison(Instruction inst) {
        return inst instanceof LCMP || inst instanceof FCMPG || inst instanceof FCMPL
                || inst instanceof DCMPG || inst instanceof DCMPL;
    }

    private boolean evaluateFloatingComparison(Instruction inst, Number a, Number b) {
        if (inst instanceof LCMP) {
            return Long.compare(a.longValue(), b.longValue()) > 0;
        } else if (inst instanceof FCMPG || inst instanceof FCMPL) {
            if (Float.isNaN(a.floatValue()) || Float.isNaN(b.floatValue())) {
                return inst instanceof FCMPG;
            }
            return Float.compare(a.floatValue(), b.floatValue()) > 0;
        } else if (inst instanceof DCMPG || inst instanceof DCMPL) {
            if (Double.isNaN(a.doubleValue()) || Double.isNaN(b.doubleValue())) {
                return inst instanceof DCMPG;
            }
            return Double.compare(a.doubleValue(), b.doubleValue()) > 0;
        }
        return false;
    }

    private void updateTargeters(InstructionHandle from, InstructionHandle to) {
        if (from.hasTargeters()) {
            for (InstructionTargeter t : from.getTargeters()) {
                t.updateTarget(from, to);
            }
        }
    }

    // CONSTANT VARIABLE FOLDING
    private boolean constantVariableFolding(ConstantPoolGen cpgen, InstructionList instList) {
        boolean modified = false;
        // map to track whether a variable might be constant
        HashMap<Integer, Boolean> constantVars = new HashMap<>();
        // map to record the literal constant value for a variable
        HashMap<Integer, Number> literalValues = new HashMap<>();
        // maps for tracking usage of variables
        HashMap<Integer, Integer> loadCounts = new HashMap<>();
        HashMap<Integer, List<InstructionHandle>> storeInstructions = new HashMap<>();

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

                // Track store instr
                storeInstructions.computeIfAbsent(idx, k -> new ArrayList<>()).add(handle);
            } else if (inst instanceof LoadInstruction) {
                // Track load counts
                int idx = ((LoadInstruction) inst).getIndex();
                loadCounts.put(idx, loadCounts.getOrDefault(idx, 0) + 1);
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
                try {
                    instList.delete(set[0]);
                } catch (TargetLostException e) {
                    for (InstructionHandle target : e.getTargets()) {
                        for (InstructionTargeter targeter : target.getTargeters()) {
                            targeter.updateTarget(target, newHandle);
                        }
                    }
                }
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
                if(result){
                    BranchInstruction newInst = new GOTO(ifInst.getTarget());
                    newHandle = instList.insert(set[0], newInst);
                    if(debug){
                        System.out.println("Folding: " + set[0].getInstruction() + " ("+val1+")"+" " + set[1].getInstruction() + " ("+val2+")" + " "+ ifInst.getName() + " => " + newInst);
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
                boolean branch = evaluateComparison(cmpResult, ifInst.getOpcode());

                // Replace with either GOTO or NOP depending on the result
                InstructionHandle newHandle = set[0].getPrev();
                if (branch){
                    BranchInstruction newInst = new GOTO(ifInst.getTarget());
                    newHandle = instList.insert(set[0], newInst);

                    if(debug){
                        System.out.println("Folding: " + set[0].getInstruction() + " ("+val1+")"+" " + set[1].getInstruction() + " ("+val2+")" + " LCMP "+ ifInst.getName() + " => " + newInst);
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

        // fifth pass-> find and replace return statements with constant expressions
        String returnPattern = "IRETURN";
        for (Iterator it = finder.search(returnPattern); it.hasNext();) {
            InstructionHandle[] set = (InstructionHandle[]) it.next();
            InstructionHandle returnHandle = set[0];
            InstructionHandle current = returnHandle.getPrev();

            // If the instruction before return is ICONST_1 (pushing true value)
            if (current != null && current.getInstruction() instanceof ICONST &&
                    ((ICONST) current.getInstruction()).getValue().intValue() == 1) {

                // Keep track of all instructions to delete
                List<InstructionHandle> toDelete = new ArrayList<>();
                InstructionHandle prev = current.getPrev();

                // Look backward through the instruction list for any constant pushes
                while (prev != null) {
                    Instruction inst = prev.getInstruction();
                    InstructionHandle prevPrev = prev.getPrev();

                    // If we find a store instruction, we need to also find its source
                    if (inst instanceof StoreInstruction) {
                        toDelete.add(prev);
                        if (prevPrev != null && isConstantPushInstruction(prevPrev.getInstruction())) {
                            toDelete.add(prevPrev);
                            prev = prevPrev.getPrev();
                        } else {
                            prev = prevPrev;
                        }
                    }
                    // If we find a constant push, it might be unused
                    else if (isConstantPushInstruction(inst)) {
                        toDelete.add(prev);
                        prev = prevPrev;
                    }
                    // If we find anything else, stop looking back
                    else {
                        break;
                    }
                }

                // Delete all the unused instructions
                if (!toDelete.isEmpty()) {
                    try {
                        for (InstructionHandle h : toDelete) {
                            instList.delete(h);
                        }
                        modified = true;
                    } catch (TargetLostException e) {
                        for (InstructionHandle target : e.getTargets()) {
                            for (InstructionTargeter targeter : target.getTargeters()) {
                                targeter.updateTarget(target, current);
                            }
                        }
                    }
                }
            }
        }

        return modified;
    }

    // Dynamic variable foldin
    private boolean dynamicVariableFolding(ConstantPoolGen cpgen, InstructionList instList) {
        boolean modified = false;

        // map to track whether a variable might be constant
        HashMap<Integer, Boolean> dynamicVars = new HashMap<>();
        // map to record the literal constant value for a variable
        HashMap<Integer, Number> literalValues = new HashMap<>();
        // maps for tracking usage of variables
        HashMap<Integer, Integer> loadCounts = new HashMap<>();
        HashMap<Integer, List<InstructionHandle>> storeInstructions = new HashMap<>();

        // first pass-> mark variables assigned via IINC or multiple stores as
        // non-constant
        for (InstructionHandle handle : instList.getInstructionHandles()) {
            Instruction inst = handle.getInstruction();
            if (inst instanceof IINC) {
                int idx = ((IINC) inst).getIndex();
                dynamicVars.put(idx, false);
            } else if (inst instanceof StoreInstruction) {
                int idx = ((StoreInstruction) inst).getIndex();

                if (dynamicVars.containsKey(idx)){
                    dynamicVars.put(idx, true);
                }else{
                    dynamicVars.put(idx, false);
                }

                // Track store instr
                storeInstructions.computeIfAbsent(idx, k -> new ArrayList<>()).add(handle);
            } else if (inst instanceof LoadInstruction) {
                // Track load counts
                int idx = ((LoadInstruction) inst).getIndex();
                loadCounts.put(idx, loadCounts.getOrDefault(idx, 0) + 1);
            }
        }

        // second pass-> record stores of possibly constant values
        String pattern = "(DSTORE | FSTORE | ISTORE | LSTORE)";
        InstructionFinder finder = new InstructionFinder(instList);
        for (Iterator it = finder.search(pattern); it.hasNext();) {
            InstructionHandle[] set = (InstructionHandle[]) it.next();
            StoreInstruction store = (StoreInstruction) set[0].getInstruction();

            InstructionHandle prev = set[0].getPrev();
            if (prev != null && isConstantPushInstruction(prev.getInstruction())) {
                PushInstruction push = (PushInstruction) prev.getInstruction();
                int idx = store.getIndex();
                if (dynamicVars.containsKey(idx) && dynamicVars.get(idx)) {
                    Number val = getConstantValue((Instruction) push, cpgen);
                    System.out.println("Dynamic variable folding: " + store + " " + push + " " + val);
                    if (val == null)
                        System.err.println("FATAL: Could not obtain literal value for unknown type");
                    else
                        literalValues.put(idx, val);
                }
            }else{

            }




            
        }

        return modified;
    }


    // Remove unreachable code
    private boolean removeUnreachableCode(ConstantPoolGen cpgen, InstructionList instList) {
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

        if(verbose){
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
                        handleTargetLost(e, storeIH.getNext());
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
