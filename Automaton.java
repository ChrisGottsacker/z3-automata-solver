import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Scanner;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import org.w3c.dom.Document;
import org.w3c.dom.NodeList;
import org.w3c.dom.Node;
import org.w3c.dom.Element;

import com.microsoft.z3.Log;
import com.microsoft.z3.Version;
import com.microsoft.z3.Z3Exception;

// This class represents one example parsed from the input file
class Example 
{
	public String description;
	public ParsedAutomaton teacherDFA;
	public ParsedAutomaton studentDFA;
}

// This class represents a single DFA
class ParsedAutomaton
{
	public int[] acceptingStates = null;
	public int initState;
	public Character[] alphabet = null;
	public int[] states = null;
	public int[][][] transitions = null;

	public ParsedAutomaton (int[] acceptingDFA, int initStateDFA, Character[] alphabetDFA, int[] statesDFA, int[][][] transitionsDFA) 
	{
		acceptingStates = acceptingDFA;
		initState = initStateDFA;
		alphabet = alphabetDFA;
		states = statesDFA;
		transitions = transitionsDFA;
	}
}

// Main class, which parses the DFAs from the input file
public class Automaton
{
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
			{
				// setting up the input DFAs for part 1
				Character alphabet[] = {'a', 'b'};
				int[] acceptingFinalStates1 = {0};
				// integer is index into alphabet[]
				int[][][] acceptingTransitions1 = {
						{{}, {0}},
						{{0}, {}}
				};

				int[] rejectingFinalStates1 = {1};
				int[][][] rejectingTransitions1 = {
						{{}, {1}},
						{{}, {1}}
				};

				// Part One
				p.getMinSepDFA(alphabet, acceptingFinalStates1, acceptingTransitions1, rejectingFinalStates1, rejectingTransitions1);

				// Part Two
				// setting up the input DFAs for part 2
				int[] acceptingFinalStates2 = {0, 2};
				int[][][] acceptingTransitions2 = {
						{{}, {1}, {0}},
						{{}, {1}, {0}},
						{{}, {1}, {0}}
				};

				p.getMinEquivalentDFA(alphabet, acceptingFinalStates2, acceptingTransitions2);

				/* Previously used DFAs for part 3 
	 			int[] teacherFinalStates = {1};
	 			int[][][] teacherTransitions = {
	 				{{1}, {0}},
	 				{{0}, {1}}
	 			};
	
	 			int[] studentFinalStates = {1,2};
	 			int[][][] studentTransitions = {
	 				{{}, {0}, {1}},
	 				{{0}, {1}, {}},
	 				{{}, {}, {0,1}}
	 			};

				
//				int[] teacherFinalStates = {0};
//				int[][][] teacherTransitions = {
//						{{}, {0,1}},
//						{{0}, {1}}
//				};
//
//				int[] studentFinalStates = {0};
//				int[][][] studentTransitions = {
//						{{}, {1}, {0}},
//						{{}, {1}, {0}},
//						{{}, {1}, {0}}
//				};
				
				p.getClosestEquivalentDFA(alphabet, teacherFinalStates, teacherTransitions, studentFinalStates, studentTransitions);
				*/

				// PART THREE
				
				// #############################################################################
				// PARSING FILE HERE
				// #############################################################################
				// retrieves an arraylist of examples, each with one studentDFA, teacherDFA and a problem description
				String filename = null;
				System.out.print("Enter a csv file: ");	// try dfa1.csv for an example
				Scanner scnr = new Scanner(System.in);
				filename = scnr.nextLine();
				
				ArrayList<Example> exs = readCSV(filename);
				
				int maxStudentStates = 0;
				int maxStudentStatesPos = 0;
				int minStudentStates = exs.get(0).studentDFA.states.length;
				int minStudentStatesPos = 0;
				for (int a = 0; a < exs.size(); a++) {
					Example ex = exs.get(a);
					// part 3
					if (ex.studentDFA.states.length > maxStudentStates) {
						maxStudentStates = ex.studentDFA.states.length;
						maxStudentStatesPos = a;
					}
						
					if (ex.studentDFA.states.length < minStudentStates) {
						minStudentStates = ex.studentDFA.states.length;
						minStudentStatesPos = a;
					}
				}
			
				long[] endtimes = new long[maxStudentStates + 1];
				long initTime = System.nanoTime();
				for (int state = minStudentStates; state <= maxStudentStates; state++) {
					System.out.println("All examples with " + state + " states:");
					int numExamplesForCurrState = 0;
					long startTime = System.nanoTime();
					for (int a = 0; a < exs.size(); a++) {
						Example ex = exs.get(a);
						if (ex.studentDFA.states.length == state) {
							System.out.println("Example " + a + ":\n");
							numExamplesForCurrState++;
							System.out.println(ex.description);
							p.getClosestEquivalentDFA(ex.teacherDFA.alphabet, ex.teacherDFA.acceptingStates, ex.teacherDFA.transitions, ex.studentDFA.acceptingStates, ex.studentDFA.transitions);
						}
					}
					long endTime = System.nanoTime();
					System.out.println(numExamplesForCurrState + " examples for state " + state);
					endtimes[state] = (endTime - startTime) / (1000000 * numExamplesForCurrState);
				}
				long finalEndTime = System.nanoTime();
				
				
				long totalDuration = (finalEndTime - initTime)/1000000;
				System.out.println("Total time: " + (float)totalDuration/1000 + " seconds");
				System.out.println("Average time per example: " + totalDuration/exs.size() + " ms");
				
				System.out.println("Max Student DFA States: " + maxStudentStates + " (at position " + maxStudentStatesPos + 
						")\nMin Student DFA States: " + minStudentStates + " (at position " + minStudentStatesPos + ")");
				
				
				System.out.println("\nAverage time by number of states: ");
				for (int state = minStudentStates; state <= maxStudentStates; state++) {
					System.out.println(state + " States: " + endtimes[state] + " ms per example");
				}
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

	// takes in a CSV file as input and parses it
	public static ArrayList<Example> readCSV(String filename) 
	{
		File f = new File(filename);
		Scanner in = null;
		try {
			in = new Scanner(f);
		} catch (FileNotFoundException e) {
			System.out.println("File not found!");
			System.exit(1);
		}

		in.useDelimiter(",|\"\n\"");

		ArrayList<Example> exs = new ArrayList<Example>();

		int feature = 0;	// to cycle between adding members of the example one at a time
		Example ex = null;
		int numExceptions = 0;
		System.out.println("Parsing all examples...");
		while (in.hasNext()) {
			int numExceptionsCurrentExample = 0;
			if (feature == 0) {	// problem description
				ex = new Example();
				ex.description = in.next();
			}
			if (feature == 1) {	// teacherDFA
				String teacherDfaXml = in.next().replace("\"", "");
				InputStream is = new ByteArrayInputStream(teacherDfaXml.getBytes());
				// parses the XML format for the teacher DFA
				Document teacher = readXML(is);
				ParsedAutomaton pDFA = null;
				try {
					// get a ParsedAutomaton (final automaton) for teacher
					pDFA = getAutomaton(teacher);
				}
				catch (Exception e) {
					numExceptions++;
					numExceptionsCurrentExample++;
				}
				ex.teacherDFA = pDFA;
			}
			if (feature == 2) {	// studentDFA
				String studentDfaXml = in.next().replace("\"", "");
				InputStream is = new ByteArrayInputStream(studentDfaXml.getBytes());
				// parses the XML format for the student DFA
				Document student = readXML(is);
				ParsedAutomaton pDFA = null;
				try {
					// get a ParsedAutomaton (final automaton) for student
					pDFA = getAutomaton(student);
				}
				catch (Exception e) {
					numExceptions++;
					numExceptionsCurrentExample++;
				}
				ex.studentDFA = pDFA;

				// if this example didn't raise any exceptions during parsing, add it to the list
				if (numExceptionsCurrentExample == 0) {
					exs.add(ex);
				}
			}

			feature = (feature+1) % 3;
		}

		System.out.println("Number of exceptions: " + numExceptions);

		return exs;
	}

	// This method reads a single DFA's XML and returns the information as a Document
	private static Document readXML(InputStream is) 
	{
		try {
			DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();

			DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();

			Document doc = dBuilder.parse(is);

			doc.getDocumentElement().normalize();
			return doc;
		} 
		catch (Exception e) {
			System.out.println("Unknown exception!");
			e.printStackTrace();
		}
		return null;
	}

	// Most of the parsing is done in this method
	private static ParsedAutomaton getAutomaton(Document doc)
	{
		Element root = doc.getDocumentElement();
		root.normalize();

		Character[] alphabetDFA = null;
		int[] statesDFA = null;
		String[][] transitionsDFA = null;
		int[][][] transitions = null;
		int[] acceptingDFA = null;
		int initStateDFA = -1;

		NodeList rootNodes = root.getChildNodes();
		for(int i = 0; i < rootNodes.getLength(); i++) {
			Node node = rootNodes.item(i);
			switch(node.getNodeName()) {

			case "alphabet":
				Element alphabet = null;
				try {
					alphabet = (Element) node;

				} catch (Exception e) {
					e.printStackTrace();
				}
				NodeList characters = alphabet.getElementsByTagName("symbol");

				alphabetDFA = new Character[characters.getLength()];
				for(int charIdx = 0; charIdx < characters.getLength(); charIdx++) {
					//System.out.println(characters.item(charIdx).getTextContent());
					alphabetDFA[charIdx] = characters.item(charIdx).getTextContent().toCharArray()[0];
				}
				break;

			case "stateSet":
				Element state = null;
				try {
					state = (Element) node;

				} catch (Exception e) {
					e.printStackTrace();
				}
				
				NodeList states = state.getElementsByTagName("state");

				statesDFA = new int[states.getLength()];
				for(int j = 0; j < states.getLength(); j++) {
					Node nNode = states.item(j);
					Element eElement = (Element) nNode;

					//System.out.println(eElement.getAttribute("sid"));
					statesDFA[j] = Integer.parseInt(eElement.getAttribute("sid"));
				}
				break;

			case "transitionSet":
				Element transition = null;
				try {
					transition = (Element) node;

				} catch (Exception e) {
					e.printStackTrace();
				}
				NodeList transitionsInDFA = transition.getElementsByTagName("transition");

				transitionsDFA = new String[statesDFA.length][statesDFA.length];
				for(int charIdx = 0; charIdx < transitionsInDFA.getLength(); charIdx++) {
					Node nNode = transitionsInDFA.item(charIdx);
					Element eElement = (Element) nNode;

					if (transitionsDFA[Integer.parseInt(eElement.getElementsByTagName("from").item(0).getTextContent())][Integer.parseInt(eElement.getElementsByTagName("to").item(0).getTextContent())] != null) {
						transitionsDFA[Integer.parseInt(eElement.getElementsByTagName("from").item(0).getTextContent())][Integer.parseInt(eElement.getElementsByTagName("to").item(0).getTextContent())] = 
								transitionsDFA[Integer.parseInt(eElement.getElementsByTagName("from").item(0).getTextContent())][Integer.parseInt(eElement.getElementsByTagName("to").item(0).getTextContent())] + eElement.getElementsByTagName("read").item(0).getTextContent();
					}
					else {
						transitionsDFA[Integer.parseInt(eElement.getElementsByTagName("from").item(0).getTextContent())][Integer.parseInt(eElement.getElementsByTagName("to").item(0).getTextContent())] = eElement.getElementsByTagName("read").item(0).getTextContent();		
					}

					transitions = new int[statesDFA.length][statesDFA.length][];

					for (int a = 0; a < transitionsDFA.length; a++) {
						for (int b = 0; b < transitionsDFA[a].length; b++) {
							if (transitionsDFA[a][b] != null) {
								int numTransitions = transitionsDFA[a][b].length();
								int[] trans = null;

								// Do this for each edge
								for (int k = 0; k < numTransitions; k++) { // go through each character on that edge
									trans = new int[numTransitions];
									int pos = 0;
									// iterate over all characters in the alphabet and find the numeric index of the given one
									for (int num = 0; num < alphabetDFA.length; num++) {
										if (alphabetDFA[num] == transitionsDFA[a][b].charAt(k))
											pos = num;
									}
									trans[k] = pos;
								}
								if (trans != null)
									transitions[a][b] = new int[numTransitions];
								transitions[a][b] = trans;
							}

						}

						// From, to and Transition on
						//System.out.println(eElement.getElementsByTagName("from").item(0).getTextContent());
						//System.out.println(eElement.getElementsByTagName("to").item(0).getTextContent());
						//System.out.println(eElement.getElementsByTagName("read").item(0).getTextContent());
					}

					for (int a = 0; a < transitions.length; a++) {
						for (int b = 0; b < transitions[a].length; b++) 
							if (transitions[a][b] == null) {
								int[] temp = {};
								transitions[a][b] = temp;	
							}
					}	
				}

				break;

			case "acceptingSet":
				Element acceptingState = null;
				try {
					acceptingState = (Element) node;

				} catch (Exception e) {
					e.printStackTrace();
				}
				NodeList acceptingStates = acceptingState.getElementsByTagName("state");

				acceptingDFA = new int[acceptingStates.getLength()];
				for(int charIdx = 0; charIdx < acceptingStates.getLength(); charIdx++) {
					Node nNode = acceptingStates.item(charIdx);
					Element eElement = (Element) nNode;

					//System.out.println(eElement.getAttribute("sid"));
					acceptingDFA[charIdx] = Integer.parseInt(eElement.getAttribute("sid"));
				}
				break;

			case "initState":
				Element initState = null;
				try {
					initState = (Element) node;

				} catch (Exception e) {
					e.printStackTrace();
				}
				NodeList initStates = initState.getElementsByTagName("state");

				Node nNode = initStates.item(0);
				Element eElement = (Element) nNode;

				//System.out.println(eElement.getAttribute("sid"));
				initStateDFA = Integer.parseInt(eElement.getAttribute("sid"));
				break;

			default:
				break;
			}
		}

		// Create a new DFA object from all the parsed information and return it
		ParsedAutomaton pDFA = new ParsedAutomaton(acceptingDFA, initStateDFA, alphabetDFA, statesDFA, transitions);

		return pDFA;
	}
}