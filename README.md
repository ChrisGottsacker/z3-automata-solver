# Automaton Finder using Z3

Z3 can be installed using instructions from https://github.com/Z3Prover/z3

The main method is in Automaton.java and it depends on Z3DFA.java
The main method would take as input a csv file (for example dfa1.csv), it would then parse it and then it would give a new DFA that is equivalent to the teacher DFA but matches the student DFA as much as possible

Other classes such as DFAResult.java and preGraphToDFA.java are representative of intermediate steps used to run Z3 efficiently.
