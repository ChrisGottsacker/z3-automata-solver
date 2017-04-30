import java.awt.List;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Arrays;
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

class Example
{
	public String description;
	public ParsedAutomaton teacherDFA;
	public ParsedAutomaton studentDFA;
}


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
			// System.out.print("Z3 Full Version String: ");
			// System.out.println(Version.getFullVersion());

			{
				// setting up the input DFAs
				Character alphabet[] = {'a', 'b'};
				int[] acceptingFinalStates = {0};
				// integer is index into alphabet[]
				int[][][] acceptingTransitions = {
						{{}, {0}},
						{{0}, {}}
				};

				int[] rejectingFinalStates = {1};
				int[][][] rejectingTransitions = {
						{{}, {1}},
						{{}, {1}}
				};

				// Part One
				p.getMinSepDFA(alphabet, acceptingFinalStates, acceptingTransitions, rejectingFinalStates, rejectingTransitions);

				// Part Two

				int[] acceptingFinalStates2 = {0, 2};
				int[][][] acceptingTransitions2 = {
						{{}, {1}, {0}},
						{{}, {1}, {0}},
						{{}, {1}, {0}}
				};

				p.getMinEquivalentDFA(alphabet, acceptingFinalStates2, acceptingTransitions2);

				int[] canonicalFinalStates = {0};
				int[][][] canonicalTransitions = {
						{{}, {0,1}},
						{{0}, {1}}
				};

				int[] proposedFinalStates = {0};
				int[][][] proposedTransitions = {
						{{}, {1}, {0}},
						{{}, {1}, {0}},
						{{}, {1}, {0}}
				};

				// #############################################################################
				// PARSING FILE HERE
				// #############################################################################
				Example ex = readCSV("dfa1.csv");
//				for (int i = 0; i < ex.teacherDFA.transitions.length; i++)
//					for (int j = 0; j < ex.teacherDFA.transitions[i].length; j++)
//					{
//						System.out.println(Arrays.toString(ex.teacherDFA.transitions));
//						for (int k = 0; k < ex.teacherDFA.transitions[i][j].length; k++)
//							System.out.println(i + " " + j + " "  + k + "     "  + ex.teacherDFA.transitions[i][j][k]);
//					}
				p.getClosestEquivalentDFA(ex.teacherDFA.alphabet, ex.teacherDFA.acceptingStates, ex.teacherDFA.transitions, ex.studentDFA.acceptingStates, ex.studentDFA.transitions);

				// p.getClosestEquivalentDFA(alphabet, canonicalFinalStates, canonicalTransitions, proposedFinalStates, proposedTransitions);
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

	public static Example readCSV(String filename)
	{
		File f = new File(filename);
		Scanner in = null;
		try {
			in = new Scanner(f);
		} catch (FileNotFoundException e) {
			System.out.println("File not found!");
		}

		in.useDelimiter(",|\"\n\"");

		ArrayList<Example> exs = new ArrayList<Example>();

		int feature = 0;	// to cycle between adding members of the example one at a time
		Example ex = new Example();
		while (in.hasNext()) {
			if (feature == 0) {
				ex.description = in.next();
			}
			if (feature == 1) {
				String teacherDfaXml = in.next().replace("\"", "");
				InputStream is = new ByteArrayInputStream(teacherDfaXml.getBytes());
				Document teacher = readXML(is);
				ParsedAutomaton pDFA = getAutomaton(teacher);
				ex.teacherDFA = pDFA;
			}
			if (feature == 2) {
				String studentDfaXml = in.next().replace("\"", "");
				InputStream is = new ByteArrayInputStream(studentDfaXml.getBytes());
				Document student = readXML(is);
				ParsedAutomaton pDFA = getAutomaton(student);
				ex.studentDFA = pDFA;
				exs.add(ex);
				break;	//remove this
			}

			feature = (feature+1) % 3;
		}

		return ex;
	}

	private static Document readXML(InputStream is)
	{
		try {
			DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();

			DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();

			Document doc = dBuilder.parse(is);

			doc.getDocumentElement().normalize();

			//			System.out.println("Root element :" + doc.getDocumentElement().getNodeName());

			return doc;
		}
		catch (Exception e) {
			System.out.println("Unknown exception!");
			e.printStackTrace();
		}
		return null;
	}

	private static ParsedAutomaton getAutomaton(Document doc)
	{
		Element root = doc.getDocumentElement();
		root.normalize();

		Character[] alphabetDFA = null;
		int[] statesDFA = null;
		String[][] transitionsDFA = null;
		int[][][] transitions = null;
		int[] acceptingDFA = null;
		int initStateDFA = 0;

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

				NodeList states = state.getElementsByTagName("label");

				statesDFA = new int[states.getLength()];
				for(int j = 0; j < states.getLength(); j++) {
					//System.out.println(states.item(j).getTextContent());
					statesDFA[j] = Integer.parseInt(states.item(j).getTextContent());
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

					//				for (int a = 0; a < transitionsDFA.length; a++) {
					//					for (int b = 0; b < transitionsDFA[a].length; b++)
					//						System.out.println(a + " " + b + " " + transitionsDFA[a][b]);
					//				}

					for (int a = 0; a < transitions.length; a++) {
						for (int b = 0; b < transitions[a].length; b++)
							if (transitions[a][b] == null) {
								int[] temp = {};
								transitions[a][b] = temp;
							}
					}
				}


				//				for (int a = 0; a < transitions.length; a++) {
				//					for (int b = 0; b < transitions[a].length; b++)
				//						if (transitions[a][b] != null)
				//							System.out.println(a + " " + b + " " + Arrays.toString(transitions[a][b]));
				//				}

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

		ParsedAutomaton pDFA = new ParsedAutomaton(acceptingDFA, initStateDFA, alphabetDFA, statesDFA, transitions);

		return pDFA;
	}
}
