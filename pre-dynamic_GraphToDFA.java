import java.util.*;
import com.microsoft.z3.*;

class GraphToDFA
{
  private void FindDFA(Context ctx) {
    System.out.println("--------------------------------------------------");
    System.out.println("\nDFA Example\n");



    Optimize opt = ctx.mkOptimize();

    int n = 2;
    int aSz = 2;
    int rSz = 2;

    Character alphabet[] = {'a', 'b'};

    int[] acceptingFinalStates = {0};
    Character[][] acceptingTransitions = {
      {null, new Character('a')},
      {new Character('a'), null}
    };

    int[] rejectingFinalStates = {1};
    Character[][] rejectingTransitions = {
      {null, new Character('b')},
      {null, new Character('b')}
    };


    BoolExpr[] finalStates = new BoolExpr[n];
    // Final states in DFA
    for (int i = 0; i < n; i++) {
    	finalStates[i] = ctx.mkBoolConst("f"+i+"");
    }

    BoolExpr[][] aNFA = new BoolExpr[n][aSz];

    //match up with accepting NFA
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < aSz; j++) {
      	 aNFA[i][j] = ctx.mkBoolConst("x"+i+""+j+"p");
      }
    }

    BoolExpr[][] rNFA = new BoolExpr[n][rSz];

    //match up with rejecting NFA
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < rSz; j++) {
      	 rNFA[i][j] = ctx.mkBoolConst("y"+i+""+j+"pp");
      }
    }

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
    opt.Assert(aNFA[0][0]);
    opt.Assert(rNFA[0][0]);

    // assert transitions from accepting NFA
    opt.Assert(ctx.mkImplies(ctx.mkAnd(aNFA[0][0], d0a0), aNFA[0][1]));
    opt.Assert(ctx.mkImplies(ctx.mkAnd(aNFA[0][0], d0a1), aNFA[1][1]));
    opt.Assert(ctx.mkImplies(ctx.mkAnd(aNFA[0][1], d0a0), aNFA[0][0]));
    opt.Assert(ctx.mkImplies(ctx.mkAnd(aNFA[0][1], d0a1), aNFA[1][0]));
    opt.Assert(ctx.mkImplies(ctx.mkAnd(aNFA[1][0], d1a0), aNFA[0][1]));
    opt.Assert(ctx.mkImplies(ctx.mkAnd(aNFA[1][0], d1a1), aNFA[1][1]));
    opt.Assert(ctx.mkImplies(ctx.mkAnd(aNFA[1][1], d1a0), aNFA[0][0]));
    opt.Assert(ctx.mkImplies(ctx.mkAnd(aNFA[1][1], d1a1), aNFA[1][0]));

    // assert transitions from rejecting NFA
    opt.Assert(ctx.mkImplies(ctx.mkAnd(rNFA[0][1], d0b0), rNFA[0][1]));
    opt.Assert(ctx.mkImplies(ctx.mkAnd(rNFA[0][1], d0b1), rNFA[1][1]));
    opt.Assert(ctx.mkImplies(ctx.mkAnd(rNFA[0][0], d0b0), rNFA[0][1]));
    opt.Assert(ctx.mkImplies(ctx.mkAnd(rNFA[0][0], d0b1), rNFA[1][1]));
    opt.Assert(ctx.mkImplies(ctx.mkAnd(rNFA[1][1], d1b0), rNFA[0][1]));
    opt.Assert(ctx.mkImplies(ctx.mkAnd(rNFA[1][1], d1b1), rNFA[1][1]));
    opt.Assert(ctx.mkImplies(ctx.mkAnd(rNFA[1][0], d1b0), rNFA[0][1]));
    opt.Assert(ctx.mkImplies(ctx.mkAnd(rNFA[1][0], d1b1), rNFA[1][1]));

    // add final-state constraints
    opt.Assert(ctx.mkImplies(aNFA[0][0], finalStates[0]));
    opt.Assert(ctx.mkImplies(aNFA[1][0], finalStates[1]));

    opt.Assert(ctx.mkImplies(rNFA[0][1], ctx.mkNot(finalStates[0])));
    opt.Assert(ctx.mkImplies(rNFA[1][1], ctx.mkNot(finalStates[1])));

    System.out.println(opt.Check());
    System.out.println(opt.getModel());
    System.out.println("\n--------------------------------------------------\n");
  }

   public static void main(String[] args)
   {
	   GraphToDFA p = new GraphToDFA();
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
}    int[] acceptingFinalStates = {0};
    Character[][] acceptingTransitions = {
      {null}, {new Character('a')},
      {new Character('a')}, {null}
    };

    int[] rejectingFinalStates = {1};
    Character[][] rejectingTransitions = {
      {null}, {new Character('b')},
      {null}, {new Character('b')}
    };
