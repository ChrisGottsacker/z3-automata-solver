import java.util.*;
import com.microsoft.z3.*;

class DFAResult
{  
   private void FindDFA(Context ctx) {
	   System.out.println("--------------------------------------------------");
	   System.out.println("\nDFA Example\n");

       Optimize opt = ctx.mkOptimize();

       // Final states in DFA
       BoolExpr f0 = ctx.mkBoolConst("f0");
       BoolExpr f1 = ctx.mkBoolConst("f1");
       
       //match up with accepting NFA
       BoolExpr x00p = ctx.mkBoolConst("x00p");
       BoolExpr x01p = ctx.mkBoolConst("x01p");
       BoolExpr x10p = ctx.mkBoolConst("x10p");
       BoolExpr x11p = ctx.mkBoolConst("x11p");
       
       // match up with rejecting NFA
       BoolExpr y00pp = ctx.mkBoolConst("y00pp");
       BoolExpr y01pp = ctx.mkBoolConst("y01pp");
       BoolExpr y10pp = ctx.mkBoolConst("y10pp");
       BoolExpr y11pp = ctx.mkBoolConst("y11pp");
       
       // transitions in DFA
       BoolExpr d0a0 = ctx.mkBoolConst("d0a0");
       BoolExpr d0a1 = ctx.mkBoolConst("d0a1");
       BoolExpr d1a0 = ctx.mkBoolConst("d1a0");
       BoolExpr d1a1 = ctx.mkBoolConst("d1a1");
       BoolExpr d0b0 = ctx.mkBoolConst("d0b0");
       BoolExpr d0b1 = ctx.mkBoolConst("d0b1");
       BoolExpr d1b0 = ctx.mkBoolConst("d1b0");
       BoolExpr d1b1 = ctx.mkBoolConst("d1b1");
       
       // assert DFA not NFA
       opt.Assert(ctx.mkOr(ctx.mkNot(d0a0), ctx.mkNot(d0a1)));
       opt.Assert(ctx.mkOr(ctx.mkNot(d1a0), ctx.mkNot(d1a1)));
       opt.Assert(ctx.mkOr(ctx.mkNot(d0b0), ctx.mkNot(d0b1)));
       opt.Assert(ctx.mkOr(ctx.mkNot(d1b0), ctx.mkNot(d1b1)));
       
       // assert DFA's transition function is total (i.e. complete DFA)
       opt.Assert(ctx.mkOr(d0a0, d0a1));
       opt.Assert(ctx.mkOr(d1a0, d1a1));
       opt.Assert(ctx.mkOr(d0b0, d0b1));
       opt.Assert(ctx.mkOr(d1b0, d1b1));
       
       // assert start states
       opt.Assert(x00p);
       opt.Assert(y00pp);
       
       // assert transitions from accepting NFA
       opt.Assert(ctx.mkImplies(ctx.mkAnd(x00p, d0a0), x01p));
       opt.Assert(ctx.mkImplies(ctx.mkAnd(x00p, d0a1), x11p));
       opt.Assert(ctx.mkImplies(ctx.mkAnd(x01p, d0a0), x00p));
       opt.Assert(ctx.mkImplies(ctx.mkAnd(x01p, d0a1), x10p));
       opt.Assert(ctx.mkImplies(ctx.mkAnd(x10p, d1a0), x01p));
       opt.Assert(ctx.mkImplies(ctx.mkAnd(x10p, d1a1), x11p));
       opt.Assert(ctx.mkImplies(ctx.mkAnd(x11p, d1a0), x00p));
       opt.Assert(ctx.mkImplies(ctx.mkAnd(x11p, d1a1), x10p));
       
       // assert transitions from rejecting NFA
       opt.Assert(ctx.mkImplies(ctx.mkAnd(y01pp, d0b0), y01pp));
       opt.Assert(ctx.mkImplies(ctx.mkAnd(y01pp, d0b1), y11pp));
       opt.Assert(ctx.mkImplies(ctx.mkAnd(y00pp, d0b0), y01pp));
       opt.Assert(ctx.mkImplies(ctx.mkAnd(y00pp, d0b1), y11pp));
       opt.Assert(ctx.mkImplies(ctx.mkAnd(y11pp, d1b0), y01pp));
       opt.Assert(ctx.mkImplies(ctx.mkAnd(y11pp, d1b1), y11pp));
       opt.Assert(ctx.mkImplies(ctx.mkAnd(y10pp, d1b0), y01pp));
       opt.Assert(ctx.mkImplies(ctx.mkAnd(y10pp, d1b1), y11pp));
      
       // add final-state constraints
       opt.Assert(ctx.mkImplies(x00p, f0));
       opt.Assert(ctx.mkImplies(x10p, f1));
       
       opt.Assert(ctx.mkImplies(y01pp, ctx.mkNot(f0)));
       opt.Assert(ctx.mkImplies(y11pp, ctx.mkNot(f1)));
       
       System.out.println(opt.Check()); 
       System.out.println(opt.getModel());
       System.out.println("\n--------------------------------------------------\n");
	}

   public static void main(String[] args)
   {
	   DFAResult p = new DFAResult();
	   try
	   {
		   com.microsoft.z3.Global.ToggleWarningMessages(true);
		   Log.open("test.log");

		   System.out.print("Z3 Major Version: ");
		   System.out.println(Version.getMajor());
		   System.out.print("Z3 Full Version: ");
		   System.out.println(Version.getString());
		   System.out.print("Z3 Full Version String: ");
		   System.out.println(Version.getFullVersion());

		   {
			   // This example needs both the model and proof generation turned on
			   HashMap<String, String> cfg = new HashMap<String, String>();
			   cfg.put("model", "true");
			   cfg.put("proof", "true");
			   Context ctx = new Context(cfg);

			   p.FindDFA(ctx);
		   }
		   Log.close();
		   if (Log.isOpen())
			   System.out.println("Log is still open!");
	   } catch (Z3Exception ex)
	   {
		   System.out.println("Z3 Managed Exception: " + ex.getMessage());
		   System.out.println("Stack trace: ");
		   ex.printStackTrace(System.out);
	   } catch (Exception ex)
	   {
		   System.out.println("Unknown Exception: " + ex.getMessage());
		   System.out.println("Stack trace: ");
		   ex.printStackTrace(System.out);
	   }
   }
}