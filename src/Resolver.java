import java.io.*;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
/**
 * This is my Resolver class. This performs the Resolution algorithm on clauses created from the 
 * knowledge base provided through 1 read in file and the theorem provided through another file. 
 * I hope you enjoy it!
 * @author Sneha Kanaujia
 *
 */

public class Resolver {

	private static HashSet<HashSet<Integer>> knowledgeBase = new HashSet<HashSet<Integer>>();
	private static List<ArrayList<Integer>> theorem = new ArrayList<ArrayList<Integer>>();
	private static HashSet<HashSet<Integer>> clauses = new HashSet<HashSet<Integer>>();
	private static int counter = 0;

	public static void main(String[] args) throws IOException	{ 
		File KBFile = new File(args[0]);
		File theoremFile = new File(args[1]);

		BufferedReader kbBR = new BufferedReader(new FileReader(KBFile));
		BufferedReader theoremBR = new BufferedReader(new FileReader(KBFile));

		/* Reads in the knowledge base file into a HashSet of HashSets
		 * The inner HashSets consist of the combinations of algebraic letters converted to negative and positive
		 * Integers based on if they've been negated or not.
		 */
		String st;
		while ((st = kbBR.readLine()) != null) {
			String[] split = st.split("\\s+");
			HashSet<Integer> hashSet = new HashSet<>();
			for(String sp: split) {
				Integer integer;
				if(sp.charAt(0) == '-') {
					integer = new Integer(-1* Character.getNumericValue(sp.charAt(1)));
					hashSet.add(integer);
				}
				else {
					integer = new Integer(Character.getNumericValue(sp.charAt(0)));
					hashSet.add(integer);
				}
			}
			knowledgeBase.add((HashSet<Integer>) hashSet);
		}

		/* Reads in the theorem (a) file into a List of ArrayLists
		 * The inner ArrayLists consist of the combinations of algebraic letters converted to negative and positive
		 * Integers based on if they've been negated or not.
		 */
		while ((st = theoremBR.readLine()) != null) {
			String[] split = st.split("\\s+");
			List<Integer> list = new ArrayList<>();
			for(String sp: split) {
				Integer integer;
				if(sp.charAt(0) == '-') {
					//Instead of negating the individual values here
					integer = new Integer(Character.getNumericValue(sp.charAt(1)));
					list.add(integer);
				}
				else {
					/* I'll negate the values here so as to mimic the change from conjunctive normal 
					 * form (CNF) to disjunctive normal form (DNF) (keep in mind the signs now change from and to or and vice versa)
					 * ex. P ⋀ Q ⋀ (¬P ⋁ R) ⋀ (¬Q ⋁ ¬R ⋁ S) (CNF) --> ¬P ⋁ ¬Q ⋁ (P ⋀ ¬R) ⋁ (Q ⋀ R ⋀ ¬S) (DNF)
					 */
					integer = new Integer(-1* Character.getNumericValue(sp.charAt(0)));
					list.add(integer);
				}
			}
			theorem.add((ArrayList<Integer>) list);	
		}

		/*Using this combinations class methods allows me to FOIL out the current DNF form of the theorem (a) which would allow 
		 * it to take on CNF form again */
		Iterator<List<Integer>> combinations = new Combinations<>(theorem);
		theorem = new ArrayList<ArrayList<Integer>>();
		while (combinations.hasNext()) {
			List<Integer> combo = combinations.next();
			boolean addToTheorem = removeTautologies(combo);
			if(addToTheorem) {
				theorem.add((ArrayList<Integer>) combo);
			}
		}

		//Add KB to the HashSets of clauses
		clauses.addAll(knowledgeBase);

		//Cycle through (-a) the theorem's clauses and add them to the clauses HashSet
		for(int i = 0; i < theorem.size(); i++) {
			HashSet<Integer> temp = new HashSet<>();
			temp.addAll(theorem.get(i));
			clauses.add(temp);
		}

		counter = clauses.size();
		//Required output:
		System.out.println(resolution() + " " + counter);

	}

	private static boolean removeTautologies(List<Integer> combo) {

		for(int i = 0; i < combo.size(); i++) {
			Integer value = combo.get(i);
			if(combo.contains(-1*value)) {
				while(combo.contains(value)) {
					combo.remove((Integer)value);
				}
				while(combo.contains(-1*value)) {
					combo.remove((Integer)(-1*value));
				}

				if(combo.isEmpty() || combo.size()<=1 || combo == null)
				{
					return false;
				}
			}
		}
		return true;
	}

	private static boolean resolution() {

		/*Use HashSet addAll func to check if you've added anything to KB --> if not (it returns false) break out
		 * Iterate through the KB using a while(true) and then keeping 2 iterators and updating and resetting one (like for loop)
		 */

		List<HashSet<Integer>> clausesList = new ArrayList<>();
		clausesList.addAll(clauses);

		List<HashSet<Integer>> newClauses = new ArrayList<>();

		//for each pair of clauses Ci, Cj in clauses do
		for(int i = 0; i < clausesList.size(); i++) {
			clausesList.clear();
			clausesList.addAll(clauses);
			HashSet<Integer> first = clausesList.get(i);

			for(int j = i+1; j < clausesList.size(); j++) {
				HashSet<Integer> second = clausesList.get(j);
				
				//resolvents ← PL-RESOLVE(Ci, Cj )
				HashSet<Integer> resolvent = new HashSet<>();
				Iterator<Integer> iter1 = first.iterator();
				
				while(iter1.hasNext()) {
					Integer variable = iter1.next();
					Integer negVariable = variable*-1;

					if(second.contains(negVariable)) {

						resolvent.addAll(first);
						resolvent.addAll(second);
						resolvent.remove(variable);
						resolvent.remove(negVariable);
						
						//if resolvents contains the empty clause then return true
						if(resolvent.isEmpty()) {
							return true;
						}
						else {
							List<Integer> res = new ArrayList<>();
							res.addAll(resolvent);
							boolean addToClauses = removeTautologies(res);
							if(addToClauses) {
								//new ← new ∪ resolvents
								newClauses.add(resolvent);
							}
						}
					}
				}//end of pair resolution/PL-RESOLVE(Ci, Cj ) while loop
			}	
		}//end of for each pair of clauses Ci, Cj in clauses do loop

		//if new ⊆ clauses then return false
		if(!newClauses.isEmpty() && clauses.containsAll(newClauses)) {
			return false;
		}

		counter += newClauses.size();
		clauses.addAll(newClauses);
		return false;
	}

}