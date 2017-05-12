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

			Z3Automata minSepDFA = getNewTargetDFA(ctx, numStates, alphabet);
			Optimize opt = minSepDFA.opt;
			addTargetDFAassertions(ctx, opt, minSepDFA);

			addAcceptingAssertions(ctx, opt, numStates, acceptingTransitions, acceptingFinalStates, minSepDFA, "X");

			addRejectingAssertions(ctx, opt, numStates, rejectingTransitions, rejectingFinalStates, minSepDFA, "Y");

			// satisfiable or unsatisfiable
			sat = opt.Check();
			if (sat == Status.SATISFIABLE) {
				minSepDFA.solve();
				minSepDFA.printModel();
			}
			numStates++;
		}
	}


	/* ########################### PART TWO ########################### */
	void getMinEquivalentDFA(Character[] alphabet, int[] acceptingFinalStates, int[][][] acceptingTransitions)
	{
		System.out.println("DFA Part 2: Get equivalent DFA of a smaller size\n");

		Context ctx = getNewContext();

		int numStates = 1;
		boolean found = false;
		Status sat = Status.UNSATISFIABLE;

		while (numStates <= acceptingTransitions.length && sat == Status.UNSATISFIABLE) {
			// Final states in DFA

			Z3Automata minEquivDFA = getNewTargetDFA(ctx, numStates, alphabet);
			Optimize opt = minEquivDFA.opt;
			addTargetDFAassertions(ctx, opt, minEquivDFA);

			BoolExpr[][] aNFA = addAcceptingAssertions(ctx, opt, numStates, acceptingTransitions, acceptingFinalStates, minEquivDFA, "X");

			addEquivalenceAssertions(ctx, opt, aNFA, acceptingFinalStates, minEquivDFA);

			sat = opt.Check();
			if (sat == Status.SATISFIABLE) {
				found = true;
				minEquivDFA.solve();
				minEquivDFA.printModel();
			}

			numStates++;
		}

		if (!found) {
			System.out.println("No smaller DFA found!");
			System.out.println("\n--------------------------------------------------\n");
		}

	}


	/* ########################### PART THREE ########################### */
	Z3Automata getClosestEquivalentDFA(Character[] alphabet, int[] canonicalFinalStates, int[][][] canonicalTransitions, int[] providedFinalStates, int[][][] providedTransitions)
	{
		// System.out.println("DFA Part 3: Get closest equivalent DFA\n");

		int numStates = Math.max(canonicalTransitions.length, providedTransitions.length);

		Context ctx = getNewContext();
		Z3Automata closestEquivalentDFA = getNewTargetDFA(ctx, numStates, alphabet);
		Optimize opt = closestEquivalentDFA.opt;
		addTargetDFAassertions(ctx, opt, closestEquivalentDFA);

		BoolExpr[][] aNFA = addAcceptingAssertions(ctx, opt, numStates, canonicalTransitions, canonicalFinalStates, closestEquivalentDFA, "X");

		addEquivalenceAssertions(ctx, opt, aNFA, canonicalFinalStates, closestEquivalentDFA);

		addSimilaritySoftAssertions(ctx, opt, providedFinalStates, providedTransitions, closestEquivalentDFA, "S");

		Status sat = opt.Check();
		if (sat == Status.SATISFIABLE) {
			closestEquivalentDFA.solve();
			// closestEquivalentDFA.printModel();
		}
		else {
			// System.out.println("Failed to generate similar, but correct, automata");
			throw new RuntimeException("Failed to generate similar, but correct, automata");
		}

		return closestEquivalentDFA;
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

		return new Z3Automata(ctx, transitions, finalStates, alphabet);
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


	private BoolExpr[][] addRejectingAssertions(Context ctx, Optimize opt, int numStates, int[][][] rejectingTransitions, int[] rejectingFinalStates, Z3Automata targetDFA, String relationName)
	{
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


	private BoolExpr[][] addAcceptingAssertions(Context ctx, Optimize opt, int numStates, int[][][] acceptingTransitions, int[] acceptingFinalStates, Z3Automata targetDFA, String relationName)
	{
		int aSz = acceptingTransitions.length;

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
						break;
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


	private void addSimilaritySoftAssertions(Context ctx, Optimize opt, int[] desiredFinalStates, int[][][] desiredTransitions, Z3Automata outputDFA, String relationName)
	{
		int transitionWt = 1;
		int finalStateWt = 1;
		// for all transitions in desired automata, add soft assertion
		for(int fromState = 0; fromState < desiredTransitions.length; fromState++) {
			for(int toState = 0; toState < desiredTransitions[0].length; toState++) {
				for(int transitionIdx = 0; transitionIdx < desiredTransitions[fromState][toState].length; transitionIdx++) {
					int transitionChar = desiredTransitions[fromState][toState][transitionIdx];
					BoolExpr softAssertion = outputDFA.transitions[fromState][transitionChar][toState];
					opt.AssertSoft(softAssertion, transitionWt, relationName);
					outputDFA.softAssertions.put(softAssertion, new Boolean(true));
				}
			}
		}

		// for all final states in desired automata, add soft assertion
		for(int fromState = 0; fromState < outputDFA.finalStates.length; fromState++) {
			boolean isFinal = false;
			for (int f = 0; f < desiredFinalStates.length; f++) {
				if(fromState == desiredFinalStates[f]) {
					isFinal = true;
					break;
				}
			}
			if(isFinal) {
				BoolExpr softAssertion = outputDFA.finalStates[fromState];
				opt.AssertSoft(softAssertion, finalStateWt, relationName);
				outputDFA.softAssertions.put(softAssertion, new Boolean(true));
			}
			else {
				BoolExpr softAssertion = outputDFA.finalStates[fromState];
				opt.AssertSoft(ctx.mkNot(softAssertion), finalStateWt, relationName);
				outputDFA.softAssertions.put(softAssertion, new Boolean(false));
			}
		}

	}

}

class Z3Automata
{
	BoolExpr[] finalStates;
	// BoolExpr[state s][transition a][state d(s,a)]
	BoolExpr[][][] transitions;
	Character[] alphabet;
	int numStates;

	Optimize opt = null;
	Model model;

	// maps soft assertions to their desired boolean value
	// e.g. finalStates[i] : true
	// this can then be used to see how many soft assertions were satisified
	HashMap<BoolExpr,Boolean> softAssertions;

	Z3Automata(Context ctx, BoolExpr[][][] transitions, BoolExpr[] finalStates, Character[] alphabet)
	{
		this.opt = ctx.mkOptimize();
		this.model = null;

		this.transitions = transitions;
		this.finalStates = finalStates;
		this.alphabet = alphabet;
		this.numStates = transitions.length;

		this.softAssertions = new HashMap<BoolExpr,Boolean>();
	}

	public void solve()
	{
		this.model = this.opt.getModel();
	}

	public int countNumChanges()
	{
		if(this.model == null || softAssertions.size() == 0){ throw new UnsupportedOperationException(); }

		int numSatisfied = 0;
		for(BoolExpr softAssertion : this.softAssertions.keySet()) {
			BoolExpr assignment = (BoolExpr) this.model.getConstInterp(softAssertion);

			boolean expectedAssignment = this.softAssertions.get(softAssertion);

			if(assignment.isTrue() == expectedAssignment) {
				numSatisfied++;
			}
		}

		return this.softAssertions.size() - numSatisfied;
	}

	// returns an array with values showing which transitions are included in the output
	private BoolExpr[][][] getTransitionAssignments()
	{
		if(this.model == null){ throw new UnsupportedOperationException(); }

		BoolExpr[][][] transAssignments = new BoolExpr[this.numStates][this.alphabet.length][this.numStates];

		for (int i = 0; i < this.numStates; i++) {
			for (int j = 0; j < this.alphabet.length; j++) {
				for (int k = 0; k < this.numStates; k++) {
					transAssignments[i][j][k] = (BoolExpr) this.model.getConstInterp(this.transitions[i][j][k]);
				}
			}
		}

		return transAssignments;
	}


	// returns an array with values showing which final states are included in the output
	private BoolExpr[] getFinalStateAssignments()
	{
		if(this.model == null){ throw new UnsupportedOperationException(); }

		BoolExpr[] finalStateAssignments = new BoolExpr[this.numStates];

		for (int i = 0; i < this.numStates; i++) {
			finalStateAssignments[i] = (BoolExpr) this.model.getConstInterp(this.finalStates[i]);
		}

		return finalStateAssignments;
	}


	public void printModel()
	{
		if(this.model == null){ throw new UnsupportedOperationException(); }

		System.out.println("SATISFIABLE with " + this.numStates + " states");
		BoolExpr[][][] transAssignments = getTransitionAssignments();
		BoolExpr[] finalStateAssignments = getFinalStateAssignments();

		printTransitions(transAssignments);
		printFinalStates(finalStateAssignments);

		// Uncomment to print the model
		// System.out.println(model);

		System.out.println("\n--------------------------------------------------\n");
	}

	/*
	* Prints all the final states in the output DFA
	*/
	private void printFinalStates(BoolExpr[] finalStateAssignments)
	{
		if(this.model == null){ throw new UnsupportedOperationException(); }

		System.out.println("\nOutput DFA Final States: ");
		for (int i = 0; i < this.numStates; i++) {
			System.out.println("State " + i + ": " + finalStateAssignments[i]);
		}
	}


	/*
	* Prints all the transitions in the output DFA
	*/
	private void printTransitions(BoolExpr[][][] transAssignments)
	{
		if(this.model == null){ throw new UnsupportedOperationException(); }

		System.out.println("\nOutput DFA Transitions: \n");
		System.out.println("From    Transition On    To    Value");
		for (int i = 0; i < this.numStates; i++) {
			for (int j = 0; j < this.alphabet.length; j++) {
				for (int k = 0; k < this.numStates; k++) {
					if (transAssignments[i][j][k].toString().equals("true"))
					System.out.println(" " + i + "            " + this.alphabet[j] + "          "  + k + "     " + transAssignments[i][j][k]);
				}
			}
		}
	}
}
