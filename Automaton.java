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

class Example
{
	public String description;
	public Document teacherDFA;
	public Document studentDFA;
}

public class Automaton
{
	public static void main(String[] args)
	{
		readCSV("dfa1.csv");
	}

	public static void readCSV(String filename)
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
				ex.teacherDFA = readXML(is);
			}
			if (feature == 2) {
				String studentDfaXml = in.next().replace("\"", "");
				InputStream is = new ByteArrayInputStream(studentDfaXml.getBytes());
				ex.studentDFA = readXML(is);
				exs.add(ex);
			}

			feature = (feature+1) % 3;
		}

		for (int i = 0; i < exs.size(); i++) {
			System.out.println("Example " + i + ": ");
			System.out.println(exs.get(i).description);
			System.out.println(exs.get(i).teacherDFA);
			System.out.println(exs.get(i).studentDFA);
			System.out.println("\n\n");
		}

		System.out.println("Num Examples: " + exs.size());
	}

	private static Document readXML(InputStream is)
	{
		try {
			DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();

			DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();

			Document doc = dBuilder.parse(is);

			Element root = doc.getDocumentElement();
			root.normalize();

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

						for(int charIdx = 0; charIdx < characters.getLength(); charIdx++) {
							System.out.println(characters.item(charIdx).getTextContent());
							System.out.println(characters.item(charIdx).getNodeName());
						}
						break;
					case "stateSet":
						break;
					case "transitionSet":
						break;
					case "acceptingSet":
						break;
					case "initState":
						break;
					default:
						break;
				}
			}

			return doc;
		}
		catch (Exception e) {
			System.out.println("Unknown exception!");
			e.printStackTrace();
		}
		return null;
	}
}
