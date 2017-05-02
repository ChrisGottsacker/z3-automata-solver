import java.util.*;

import com.microsoft.z3.*;

class Z3DFA
{
	/* ########################### PART ONE ########################### */
	void getMinSepDFA(Character[] alphabet, int[] acceptingFinalStates, int[][][] acceptingTransitions, int[] rejectingFinalStates, int[][][] rejectingTransitions)
	{
		System.out.println("--------------------------------------------------");
		System.out.println("\nDFA Part 1: Get Output DFA from accepting and rejecting DFAs\n");

		Context ctx = getNewContext();

		Status sat = Status.UNSATISFIABLE;
		int numStates = 1;

		// go in a loop and find the min number of states which are satisfiable
		while (sat == Status.UNSATISFIABLE) {
			Optimize opt = ctx.mkOptimize();

			Z3Automata minSepDFA = getNewTargetDFA(ctx, numStates, alphabet);
			addTargetDFAassertions(ctx, opt, minSepDFA);

			addAcceptingAssertions(ctx, opt, numStates, acceptingTransitions, acceptingFinalStates, minSepDFA, "X");

			addRejectingAssertions(ctx, opt, numStates, rejectingTransitions, rejectingFinalStates, minSepDFA, "Y");

			// satisfiable or unsatisfiable
			sat = opt.Check();
			if (sat == Status.SATISFIABLE) {
				printModel(opt, minSepDFA);
			}
			numStates++;
		}
	}

	/* ########################### PART TWO ########################### */
	void getMinEquivalentDFA(Character[] alphabet, int[] acceptingFinalStates, int[][][] acceptingTransitions) {
		System.out.println("DFA Part 2: Get equivalent DFA of a smaller size\n");

		Context ctx = getNewContext();

		int numStates = 1;
		boolean found = false;
		Status sat = Status.UNSATISFIABLE;

		while (numStates <= acceptingTransitions.length && sat == Status.UNSATISFIABLE) {
			// Final states in DFA
			Optimize opt = ctx.mkOptimize();

			Z3Automata minEquivDFA = getNewTargetDFA(ctx, numStates, alphabet);
			addTargetDFAassertions(ctx, opt, minEquivDFA);

			BoolExpr[][] aNFA = addAcceptingAssertions(ctx, opt, numStates, acceptingTransitions, acceptingFinalStates, minEquivDFA, "X");

			addEquivalenceAssertions(ctx, opt, aNFA, acceptingFinalStates, minEquivDFA);

			sat = opt.Check();
			if (sat == Status.SATISFIABLE) {
				found = true;
				printModel(opt, minEquivDFA);
			}

			numStates++;
		}

		if (!found) {
			System.out.println("No smaller DFA found!");
			System.out.println("\n--------------------------------------------------\n");
		}

	}

	/* ########################### PART THREE ########################### */
	void getClosestEquivalentDFA(Character[] alphabet, int[] canonicalFinalStates, int[][][] canonicalTransitions, int[] providedFinalStates, int[][][] providedTransitions)
	{
		System.out.println("DFA Part 3: Get closest equivalent DFA\n");

		int numStates = Math.max(canonicalTransitions.length, providedTransitions.length);

		Context ctx = getNewContext();
		Optimize opt = ctx.mkOptimize();
		Z3Automata closestEquivalentDFA = getNewTargetDFA(ctx, numStates, alphabet);
		addTargetDFAassertions(ctx, opt, closestEquivalentDFA);

		BoolExpr[][] aNFA = addAcceptingAssertions(ctx, opt, numStates, canonicalTransitions, canonicalFinalStates, closestEquivalentDFA, "X");

		addEquivalenceAssertions(ctx, opt, aNFA, canonicalFinalStates, closestEquivalentDFA);

		// addSimilaritySoftAssertions()

		Status sat = opt.Check();
		if (sat == Status.SATISFIABLE) {
			printModel(opt, closestEquivalentDFA);
		}
		else {
			System.out.println("Failed to generate similar, but correct, automata");
		}
	}

	private Context getNewContext()
	{
		HashMap<String, String> cfg = new HashMap<String, String>();
		// Turn on model generation
		cfg.put("model", "true");
		// cfg.put("proof", "true");
		return new Context(cfg);
	}

	private Z3Automata getNewTargetDFA(Context ctx, int numStates, Character[] alphabet)
	{
		BoolExpr[] finalStates = new BoolExpr[numStates];
		for (int i = 0; i < numStates; i++) {
			finalStates[i] = ctx.mkBoolConst("f("+i+")");
		}

		BoolExpr[][][] transitions = new BoolExpr[numStates][alphabet.length][numStates];

		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < alphabet.length; j++) {
				for (int k = 0; k < numStates; k++) {
					transitions[i][j][k] = ctx.mkBoolConst("d("+i+","+alphabet[j]+")="+k+"");
				}
			}
		}

		return new Z3Automata(transitions, finalStates, alphabet);
	}

	private void addTargetDFAassertions(Context ctx, Optimize opt, Z3Automata targetDFA)
	{
		// assert DFA not NFA
		for (int j = 0; j < targetDFA.alphabet.length; j++) {
			for (int i = 0; i < targetDFA.numStates; i++) {
				BoolExpr bexp = ctx.mkBool(false);
				for (int k = 0; k < targetDFA.numStates; k++) {
					bexp = ctx.mkOr(ctx.mkNot(targetDFA.transitions[i][j][k]), bexp);
				}
				opt.Assert(bexp);
			}
		}

		// assert DFA's transition function is total (i.e. complete DFA)
		for (int j = 0; j < targetDFA.alphabet.length; j++) {
			for (int i = 0; i < targetDFA.numStates; i++) {
				BoolExpr bexp = ctx.mkBool(false);
				for (int k = 0; k < targetDFA.numStates; k++) {
					bexp = ctx.mkOr(targetDFA.transitions[i][j][k], bexp);
				}
				opt.Assert(bexp);
			}
		}
	}


	private BoolExpr[][] addRejectingAssertions(Context ctx, Optimize opt, int numStates, int[][][] rejectingTransitions, int[] rejectingFinalStates, Z3Automata targetDFA, String relationName){
		int rSz = rejectingTransitions.length;

		//match up with rejecting NFA
		BoolExpr[][] rNFA = new BoolExpr[numStates][rSz];
		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < rSz; j++) {
				rNFA[i][j] = ctx.mkBoolConst(relationName + "("+i+","+j+")");
			}
		}

		// assert start states
		opt.Assert(rNFA[0][0]);

		// assert transitions from rejecting NFA
		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < rSz; j++) {
				for (int k = 0; k < numStates; k++) {
					for (int l = 0; l < rSz; l++) {
						for (int m = 0; m < rejectingTransitions[j][l].length; m++){
							opt.Assert(ctx.mkImplies(ctx.mkAnd(rNFA[i][j], targetDFA.transitions[i][ rejectingTransitions[j][l][m] ][k]), rNFA[k][l]));
						}
					}
				}
			}
		}

		// add final-state constraints
		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < rejectingFinalStates.length; j++) {
				opt.Assert(ctx.mkImplies(rNFA[i][rejectingFinalStates[j]], ctx.mkNot(targetDFA.finalStates[i])));
			}
		}

		return rNFA;
	}

	private BoolExpr[][] addAcceptingAssertions(Context ctx, Optimize opt, int numStates, int[][][] acceptingTransitions,
			int[] acceptingFinalStates, Z3Automata targetDFA, String relationName){
		int aSz = acceptingTransitions.length;
		int transitionWt = 1;
		int finalStateWt = 1;

		//match up with accepting NFA
		BoolExpr[][] aNFA = new BoolExpr[numStates][aSz];
		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < aSz; j++) {
				aNFA[i][j] = ctx.mkBoolConst(relationName + "("+i+","+j+")");
			}
		}

		// assert start states
		opt.Assert(aNFA[0][0]);

		// assert transitions from accepting NFA
		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < aSz; j++) {
				for (int k = 0; k < numStates; k++) {
					for (int l = 0; l < aSz; l++) {
						if (acceptingTransitions[j][l] != null)
							for (int m = 0; m < acceptingTransitions[j][l].length; m++){
								opt.Assert(ctx.mkImplies(ctx.mkAnd(aNFA[i][j], targetDFA.transitions[i][ acceptingTransitions[j][l][m] ][k]), aNFA[k][l]));
							}
					}
				}
			}
		}

		// add final-state constraints
		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < acceptingFinalStates.length; j++) {
					opt.Assert(ctx.mkImplies(aNFA[i][ acceptingFinalStates[j]], targetDFA.finalStates[i]));
			}
		}

		return aNFA;
	}


	private void addEquivalenceAssertions(Context ctx, Optimize opt, BoolExpr[][] aNFA, int[] acceptingFinalStates, Z3Automata minEquivDFA)
	{
		for (int i = 0; i < aNFA.length; i++) {
			for (int j = 0; j < aNFA[i].length; j++) {
				boolean isFinal = false;
				for (int a = 0; a < acceptingFinalStates.length; a++) {
					if(j == acceptingFinalStates[a]) {
						isFinal = true;
					}
				}
				if(isFinal) {
					opt.Assert(ctx.mkImplies(ctx.mkNot(minEquivDFA.finalStates[i]), ctx.mkNot(aNFA[i][j])));
				}
				else {
					opt.Assert(ctx.mkImplies(minEquivDFA.finalStates[i], ctx.mkNot(aNFA[i][j])));
				}
			}
		}
	}


	// returns an array with values showing which transitions are included in the output
	private BoolExpr[][][] getTransitionAssignments(Model model, BoolExpr[][][] trans, int numStates, int alphaLen)
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
	private BoolExpr[] getFinalStateAssignments(Model model, BoolExpr[] finalStates, int numStates)
	{
		BoolExpr[] finalStateAssignments = new BoolExpr[numStates];

		for (int i = 0; i < numStates; i++) {
			finalStateAssignments[i] = (BoolExpr) model.getConstInterp(finalStates[i]);
		}

		return finalStateAssignments;
	}


	private void printModel(Optimize opt, Z3Automata targetDFA)
	{
		System.out.println("SATISFIABLE with " + targetDFA.numStates + " states");
		Model model = opt.getModel();
		BoolExpr[][][] transAssignments = getTransitionAssignments(model, targetDFA.transitions, targetDFA.numStates, targetDFA.alphabet.length);
		BoolExpr[] finalStateAssignments = getFinalStateAssignments(model, targetDFA.finalStates, targetDFA.numStates);

		printTransitions(transAssignments, targetDFA.numStates, targetDFA.alphabet);
		printFinalStates(finalStateAssignments, targetDFA.numStates);

		// Uncomment to print the model
		// System.out.println(model);

		System.out.println("\n--------------------------------------------------\n");
	}

	/*
	 * Prints all the final states in the output DFA
	 */
	private void printFinalStates(BoolExpr[] finalStateAssignments, int numStates)
	{
		System.out.println("\nOutput DFA Final States: ");
		for (int i = 0; i < numStates; i++) {
			System.out.println("State " + i + ": " + finalStateAssignments[i]);
		}
	}

	/*
	 * Prints all the transitions in the output DFA
	 */
	private void printTransitions(BoolExpr[][][] transAssignments, int numStates, Character[] alphabet)
	{
		System.out.println("\nOutput DFA Transitions: \n");
		System.out.println("From    Transition On    To    Value");
		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < alphabet.length; j++) {
				for (int k = 0; k < numStates; k++) {
					if (transAssignments[i][j][k].toString().equals("true"))
						System.out.println(" " + i + "            " + alphabet[j] + "          "  + k + "     " + transAssignments[i][j][k]);
				}
			}
		}
	}

	/* ########################### PART TWO ########################### */



	// public static void main(String[] args)
	// {
	// 	Z3DFA p = new Z3DFA();
	// 	try
	// 	{
	// 		com.microsoft.z3.Global.ToggleWarningMessages(true);
	// 		Log.open("test.log");
	//
	// 		System.out.print("Z3 Major Version: ");
	// 		System.out.println(Version.getMajor());
	// 		System.out.print("Z3 Full Version: ");
	// 		System.out.println(Version.getString());
	// 		// System.out.print("Z3 Full Version String: ");
	// 		// System.out.println(Version.getFullVersion());
	//
	// 		{
	// 			// // setting up the input DFAs
	// 			Character alphabet[] = {'a', 'b'};
	// 			// int[] acceptingFinalStates = {0};
	// 			// // integer is index into alphabet[]
	// 			// int[][][] acceptingTransitions = {
	// 			// 		{{}, {0}},
	// 			// 		{{0}, {}}
	// 			// };
	// 			//
	// 			// int[] rejectingFinalStates = {1};
	// 			// int[][][] rejectingTransitions = {
	// 			// 		{{}, {1}},
	// 			// 		{{}, {1}}
	// 			// };
	// 			//
	// 			// // Part One
	// 			// p.getMinSepDFA(alphabet, acceptingFinalStates, acceptingTransitions, rejectingFinalStates, rejectingTransitions);
	// 			//
	// 			// // Part Two
	// 			//
	// 			// int[] acceptingFinalStates2 = {0, 2};
	// 			// int[][][] acceptingTransitions2 = {
	// 			// 	{{}, {1}, {0}},
	// 			// 	{{}, {1}, {0}},
	// 			// 	{{}, {1}, {0}}
	// 			// };
	// 			//
	// 			// p.getMinEquivalentDFA(alphabet, acceptingFinalStates2, acceptingTransitions2);
	//
	// 			int[] canonicalFinalStates = {1};
	// 			int[][][] canonicalTransitions = {
	// 				{{1}, {0}},
	// 				{{0}, {1}}
	// 			};
	//
	// 			int[] proposedFinalStates = {0};
	// 			int[][][] proposedTransitions = {
	// 				{{}, {0}, {1}},
	// 				{{0}, {1}, {}},
	// 				{{}, {}, {0,1}}
	// 			};
	//
	// 			p.getClosestEquivalentDFA(alphabet, canonicalFinalStates, canonicalTransitions, proposedFinalStates, proposedTransitions);
	// 		}
	// 		Log.close();
	// 		if (Log.isOpen())
	// 			System.out.println("Log is still open!");
	// 	} catch (Z3Exception ex)
	// 	{
	// 		System.out.println("Z3 Managed Exception: " + ex.getMessage());
	// 		System.out.println("Stack trace: ");
	// 		ex.printStackTrace(System.out);
	// 	} catch (Exception ex)
	// 	{
	// 		System.out.println("Unknown Exception: " + ex.getMessage());
	// 		System.out.println("Stack trace: ");
	// 		ex.printStackTrace(System.out);
	// 	}
	// }
}

class Z3Automata {
	BoolExpr[] finalStates;
	// BoolExpr[state s][transition a][state d(s,a)]
	BoolExpr[][][] transitions;
	Character[] alphabet;
	int numStates;

	Z3Automata(BoolExpr[][][] transitions, BoolExpr[] finalStates, Character[] alphabet)
	{
		this.transitions = transitions;
		this.finalStates = finalStates;
		this.alphabet = alphabet;
		this.numStates = transitions.length;
	}
}
