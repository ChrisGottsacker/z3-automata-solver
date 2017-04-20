import java.util.*;

import com.microsoft.z3.*;

class Z3DFA
{  
  private void FindDFA(Context ctx) 
  {
    System.out.println("--------------------------------------------------");
    System.out.println("\nDFA Example\n");

    String sat = "UNSATISFIABLE";
    int numStates = 1;
    
    // go in a loop and find the min number of states which are satisfiable
    while (sat.equals("UNSATISFIABLE")) {
    	Optimize opt = ctx.mkOptimize();
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
	
	    // Final states in DFA
	    BoolExpr[] finalStates = new BoolExpr[numStates];
	    for (int i = 0; i < numStates; i++) {
	    	finalStates[i] = ctx.mkBoolConst("f"+i+"");
	    }
	
	    //match up with accepting NFA
	    BoolExpr[][] aNFA = new BoolExpr[numStates][aSz];
	    for (int i = 0; i < numStates; i++) {
	      for (int j = 0; j < aSz; j++) {
	      	 aNFA[i][j] = ctx.mkBoolConst("x"+i+""+j);
	      }
	    }
	
	    //match up with rejecting NFA
	    BoolExpr[][] rNFA = new BoolExpr[numStates][rSz];
	    for (int i = 0; i < numStates; i++) {
	      for (int j = 0; j < rSz; j++) {
	      	 rNFA[i][j] = ctx.mkBoolConst("y"+i+""+j);
	      }
	    }
	
	    // transitions in DFA
	    BoolExpr[][][] trans = new BoolExpr[numStates][alphabet.length][numStates];
	    
	    for (int i = 0; i < numStates; i++) {
	    	 for (int j = 0; j < alphabet.length; j++) { 
	         	for (int k = 0; k < numStates; k++) {
	            	trans[i][j][k] = ctx.mkBoolConst("d"+i+""+alphabet[j]+""+k+"");
	            }
	         }
	    }
	
	    // assert DFA not NFA
	    for (int j = 0; j < alphabet.length; j++) {
	    	for (int i = 0; i < numStates; i++) {
	    		BoolExpr bexp = ctx.mkBool(false);
	    		for (int k = 0; k < numStates; k++) {
	    			bexp = ctx.mkOr(ctx.mkNot(trans[i][j][k]), bexp);
	    		} 	
	    		opt.Assert(bexp);
	    	}
	    }
	
	    // assert DFA's transition function is total (i.e. complete DFA)
	    for (int j = 0; j < alphabet.length; j++) {
	    	for (int i = 0; i < numStates; i++) {
	    		BoolExpr bexp = ctx.mkBool(false);
	    		for (int k = 0; k < numStates; k++) {
	    			bexp = ctx.mkOr(trans[i][j][k], bexp);
	    		} 	
	    		opt.Assert(bexp);
	    	}
	    }
	
	    // assert start states
	    opt.Assert(aNFA[0][0]);
	    opt.Assert(rNFA[0][0]);
	
	    // assert transitions from accepting NFA
	    for (int i = 0; i < numStates; i++) {
	    	for (int j = 0; j < aSz; j++) {
	        	for (int k = 0; k < numStates; k++) {
	            	for (int l = 0; l < aSz; l++) {
	                	if (acceptingTransitions[j][l] >= 0) {
	                		opt.Assert(ctx.mkImplies(ctx.mkAnd(aNFA[i][j], trans[i][ acceptingTransitions[j][l] ][k]), aNFA[k][l]));
	                  	}
	              	}
	          	}
	      	}
	    }
	
	    // assert transitions from rejecting NFA
	    for (int i = 0; i < numStates; i++) {
	    	for (int j = 0; j < rSz; j++) {
	        	for (int k = 0; k < numStates; k++) {
	            	for (int l = 0; l < rSz; l++) {
	                	if (rejectingTransitions[j][l] >= 0) {
	                    	opt.Assert(ctx.mkImplies(ctx.mkAnd(rNFA[i][j], trans[i][ rejectingTransitions[j][l] ][k]), rNFA[k][l]));
	                  	}
	              	}
	          	}
	      	}
	    }
	
	    // add final-state constraints
	    for (int i = 0; i < numStates; i++) {
	        for (int j = 0; j < acceptingFinalStates.length; j++) {
	              opt.Assert(ctx.mkImplies(aNFA[i][ acceptingFinalStates[j]], finalStates[i]));       	 
	        }
	      }
	    
	    for (int i = 0; i < numStates; i++) {
	    	for (int j = 0; j < rejectingFinalStates.length; j++) {
	        	opt.Assert(ctx.mkImplies(rNFA[i][rejectingFinalStates[j]], ctx.mkNot(finalStates[i])));
	        }
	    }
	
	    // satisfiable or unsatisfiable
	    sat = opt.Check().toString();
		if (sat.equals("SATISFIABLE")) {
		    System.out.println(sat + " with " + numStates + " states"); 
		    Model model = opt.getModel();
		    BoolExpr[][][] transAssignments = TransitionsAssignments(model, trans, numStates, alphabet.length);
		    BoolExpr[] finalStateAssignments = FinalStateAssignments(model, finalStates, numStates);
		    
		    PrintTransitions(transAssignments, numStates, alphabet);
		    PrintFinalStates(finalStateAssignments, numStates);		    
		    
		    // Uncomment to print the model
		    // System.out.println(model);
		    
		    System.out.println("\n--------------------------------------------------\n");
		}
		numStates++;
    }
  }

  // returns an array with values showing which transitions are included in the output
  private BoolExpr[][][] TransitionsAssignments(Model model, BoolExpr[][][] trans, int numStates, int alphaLen) 
  {
	
	BoolExpr[][][] transAssignments = new BoolExpr[numStates][alphaLen][numStates];
	
	for (int i = 0; i < numStates; i++) {
		for (int j = 0; j < alphaLen; j++) {
			for (int k = 0; k < numStates; k++) {
				transAssignments[i][j][k] = (BoolExpr) model.getConstInterp(trans[i][j][k]);
			}
		}
	}
		
	return transAssignments;
  }

  // returns an array with values showing which final states are included in the output
  private BoolExpr[] FinalStateAssignments(Model model, BoolExpr[] finalStates, int numStates) 
  {
	BoolExpr[] finalStateAssignments = new BoolExpr[numStates];
	
	for (int i = 0; i < numStates; i++) {
		finalStateAssignments[i] = (BoolExpr) model.getConstInterp(finalStates[i]);
	}
	
	return finalStateAssignments;
  }
  
  /*
   * Prints all the final states in the output DFA
   */
  private void PrintFinalStates(BoolExpr[] finalStateAssignments, int numStates) 
  {
	  System.out.println("\nOutput DFA Final States: ");
	  for (int i = 0; i < numStates; i++) {
			System.out.println("State " + i + ": " + finalStateAssignments[i]);
	  }
  }

  /*
   * Prints all the transitions in the output DFA
   */
  private void PrintTransitions(BoolExpr[][][] transAssignments, int numStates, Character[] alphabet) 
  {
	  System.out.println("\nOutput DFA Transitions: \n");
	  System.out.println("From    Transition On    To    Value");
	  for (int i = 0; i < numStates; i++) {
		  for (int j = 0; j < alphabet.length; j++) {
			  for (int k = 0; k < numStates; k++) {
				  if (transAssignments[i][j][k].toString().equals("true"))
					  System.out.println(" " + i + "          " + alphabet[j] + "            "  + k + "     " + transAssignments[i][j][k]);
			  }
		  }
	  }
  }
	

  public static void main(String[] args)
  {
	  Z3DFA p = new Z3DFA();
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