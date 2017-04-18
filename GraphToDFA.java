import java.util.*;
import com.microsoft.z3.*;

class GraphToDFA
{  
  private void FindDFA(Context ctx) {
    System.out.println("--------------------------------------------------");
    System.out.println("\nDFA Example\n");



    Optimize opt = ctx.mkOptimize();

    int n = 5;
    int aSz = 2;
    int rSz = 2;
    Character alphabet[] = {'a', 'b'};
    int[] acceptingFinalStates = {0};
    // -1 if no transitions from that state, 0 for 'a' transition, 1 for 'b' transition
    int[][] acceptingTransitions = {
      {-1, 0},
      {0, -1}
    };

    int[] rejectingFinalStates = {1};
    // -1 if no transitions from that state, 0 for 'a' transition, 1 for 'b' transition
    int[][] rejectingTransitions = {
      {-1, 1},
      {-1, 1}
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

    // transitions in DFA
    BoolExpr[][][] trans = new BoolExpr[n][alphabet.length][n];
    
    for (int i = 0; i < n; i++) {
    	 for (int j = 0; j < alphabet.length; j++) { 
         	for (int k = 0; k < n; k++) {
            	trans[i][j][k] = ctx.mkBoolConst("d"+i+""+alphabet[j]+""+k+"");
            }
         }
    }

    // assert DFA not NFA
    for (int j = 0; j < alphabet.length; j++) {
	  for (int i = 0; i < n; i++) {
	    for (int k = 0; k < n; k++) {
	      for (int l = n-1; l > k; l--) {
	      	opt.Assert(ctx.mkOr(ctx.mkNot(trans[i][j][k]), ctx.mkNot(trans[i][j][l])));
	      }
	    } 	
	  }
    }

    // assert DFA's transition function is total (i.e. complete DFA)
    for (int j = 0; j < alphabet.length; j++) {
    	for (int i = 0; i < n; i++) {
        	for (int k = 0; k < n; k++) {
                for (int l = n-1; l > k; l--) {
                	opt.Assert(ctx.mkOr(trans[i][j][k], trans[i][j][l]));
                }
        	}
        }
    }

    // assert start states
    opt.Assert(aNFA[0][0]);
    opt.Assert(rNFA[0][0]);

    // assert transitions from accepting NFA
    for (int i = 0; i < n; i++) {
    	for (int j = 0; j < aSz; j++) {
        	for (int k = 0; k < n; k++) {
            	for (int l = 0; l < aSz; l++) {
                	if (acceptingTransitions[j][l] >= 0) {
                		opt.Assert(ctx.mkImplies(ctx.mkAnd(aNFA[i][j], trans[i][ acceptingTransitions[j][l] ][k]), aNFA[k][l]));
                  	}
              	}
          	}
      	}
    }

    // assert transitions from rejecting NFA
    for (int i = 0; i < n; i++) {
    	for (int j = 0; j < rSz; j++) {
        	for (int k = 0; k < n; k++) {
            	for (int l = 0; l < rSz; l++) {
                	if (rejectingTransitions[j][l] >= 0) {
                    	opt.Assert(ctx.mkImplies(ctx.mkAnd(rNFA[i][j], trans[i][ rejectingTransitions[j][l] ][k]), rNFA[k][l]));
                  	}
              	}
          	}
      	}
    }

    // add final-state constraints
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < acceptingFinalStates.length; j++) {
              opt.Assert(ctx.mkImplies(aNFA[i][ acceptingFinalStates[j]], finalStates[i]));       	 
        }
      }
    
    for (int i = 0; i < n; i++) {
    	for (int j = 0; j < rejectingFinalStates.length; j++) {
        	opt.Assert(ctx.mkImplies(rNFA[i][rejectingFinalStates[j]], ctx.mkNot(finalStates[i])));
        }
    }

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
}