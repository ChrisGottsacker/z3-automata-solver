import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Scanner;

class Example 
{
	public String description;
	public String teacherDFA;
	public String studentDFA;
}

public class Automaton 
{
	public static void main(String[] args) 
	{
		File f = new File("dfa1.csv");
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
			if (feature == 0)
				ex.description = in.next();
			if (feature == 1)
				ex.teacherDFA = in.next().replace("\"", "");
			if (feature == 2) {
				ex.studentDFA = in.next().replace("\"", "");
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
}
