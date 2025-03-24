package comp0012.main;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Iterator;

import org.apache.bcel.classfile.ClassParser;
import org.apache.bcel.classfile.Code;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.*;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.util.InstructionFinder;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.TargetLostException;



public class ConstantFolder
{
	ClassParser parser = null;
	ClassGen gen = null;

	JavaClass original = null;
	JavaClass optimized = null;

	public ConstantFolder(String classFilePath)
	{
		try{
			this.parser = new ClassParser(classFilePath);
			this.original = this.parser.parse();
			this.gen = new ClassGen(this.original);
		} catch(IOException e){
			e.printStackTrace();
		}
	}
	
	public void optimize()
	{
		ClassGen cgen = new ClassGen(original);
		ConstantPoolGen cpgen = cgen.getConstantPool();

		// Implement your optimization here
		for(Method method: gen.getMethods()){
		    MethodGen methodGen = new MethodGen(method, gen.getClassName(), cpgen);
		    InstructionList il = methodGen.getInstructionList();
		    if(il == null)continue;
		    InstructionList working_list = il.copy();
		    InstructionFinder finder = new InstructionFinder(il);
		    String[] patterns = {
                    "ICONST ICONST (IADD|ISUB|IMUL|IDIV)",
                    "LCONST LCONST (LADD|LSUB|LMUL|LDIV)",
                    "FCONST FCONST (FADD|FSUB|FMUL|FDIV)",
                    "DCONST DCONST (DADD|DSUB|DMUL|DDIV)",
		    "ICONST ICONST (IF_ICMPGT|IF_ICMPLT|IF_ICMPEQ)",
                    "LCONST LCONST (LCMP)"
                    };
		    boolean modified = false;
		    for(String pattern: patterns){
		        for(Iterator<InstructionHandle[]> it = finder.search(pattern); it.hasNext();){
			    InstructionHandle[] match = it.next();
			    Number const1 = get_constant_value(match[0].getInstruction());
			    Number const2 = get_constant_value(match[1].getInstruction());
			    Instruction arithmetic_op = match[2].getInstruction();
			    if(const1 == null || const2 == null)continue;
			    Number result = compute_arithmetic_result(const1, const2, arithmetic_op);
			    if(result != null){
			        try{
			            InstructionHandle new_instruction = il.insert(match[0], get_push_instruction(result));
			            working_list.delete(match[0]);
				    working_list.delete(match[1]);
				    working_list.delete(match[2]);
				    modified = true;
			        }
			        catch(TargetLostException e){
			            e.printStackTrace();
			        }
			    }

			    Boolean comparison_result = compute_comparison_result(const1, const2, arithmetic_op);
			    if(comparison_result != null){
			        try{
				    InstructionHandle new_instruction = il.insert(match[0], new ICONST(comparison_result ? 1:0));
				    working_list.delete(match[0]);
				    working_list.delete(match[1]);
				    working_list.delete(match[2]);
				    modified = true;
				}
				catch(TargetLostException e){
				    e.printStackTrace();
				}
			    }
			}
		    }
		    if(modified){
			methodGen.setInstructionList(working_list);
			methodGen.setMaxStack();
			methodGen.setMaxLocals();
			Method optimised = methodGen.getMethod();
			gen.replaceMethod(method, optimised);
		    }

		}
        
		this.optimized = gen.getJavaClass();
	}
	private Number get_constant_value(Instruction instruction) {
            if (instruction instanceof ConstantPushInstruction) {
                return ((ConstantPushInstruction) instruction).getValue();
            }
            return null;
        }

    	private Number compute_arithmetic_result(Number val1, Number val2, Instruction op) {
            if (op instanceof IADD) return val1.intValue() + val2.intValue();
            if (op instanceof ISUB) return val1.intValue() - val2.intValue();
            if (op instanceof IMUL) return val1.intValue() * val2.intValue();
            if (op instanceof IDIV && val2.intValue() != 0) return val1.intValue() / val2.intValue();

            if (op instanceof LADD) return val1.longValue() + val2.longValue();
            if (op instanceof LSUB) return val1.longValue() - val2.longValue();
            if (op instanceof LMUL) return val1.longValue() * val2.longValue();
            if (op instanceof LDIV && val2.longValue() != 0) return val1.longValue() / val2.longValue();

            if (op instanceof FADD) return val1.floatValue() + val2.floatValue();
            if (op instanceof FSUB) return val1.floatValue() - val2.floatValue();
            if (op instanceof FMUL) return val1.floatValue() * val2.floatValue();
            if (op instanceof FDIV && val2.floatValue() != 0) return val1.floatValue() / val2.floatValue();

            if (op instanceof DADD) return val1.doubleValue() + val2.doubleValue();
            if (op instanceof DSUB) return val1.doubleValue() - val2.doubleValue();
            if (op instanceof DMUL) return val1.doubleValue() * val2.doubleValue();
            if (op instanceof DDIV && val2.doubleValue() != 0) return val1.doubleValue() / val2.doubleValue();

            return null;
        }

	private Boolean compute_comparison_result(Number val1, Number val2, Instruction op){
	    if(op instanceof IF_ICMPGT)return val1.intValue() > val2.intValue();
	    if (op instanceof IF_ICMPLT) return val1.intValue() < val2.intValue();
            if (op instanceof IF_ICMPEQ) return val1.intValue() == val2.intValue();
            if (op instanceof LCMP) return val1.longValue() > val2.longValue();
	    return null;
	}

	private Instruction get_push_instruction(Number value) {
            if (value instanceof Integer) return new ICONST(value.intValue());
            if (value instanceof Long) return new LCONST(value.longValue());
            if (value instanceof Float) return new FCONST(value.floatValue());
            if (value instanceof Double) return new DCONST(value.doubleValue());
            return null;
	}

	
	public void write(String optimisedFilePath)
	{
		this.optimize();

		try {
			FileOutputStream out = new FileOutputStream(new File(optimisedFilePath));
			this.optimized.dump(out);
		} catch (FileNotFoundException e) {
			// Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// Auto-generated catch block
			e.printStackTrace();
		}
	}
}
