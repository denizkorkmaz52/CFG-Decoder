

// -- Description -- 
// Assume 'S' is always the start symbol 
// You may assume that your method will be tested in the following setting: 
// - grammar will contain between 1 and 100 strings, 
// - each string will represent one production (possibly with multiple right 
// hand sides, separated by | (see examples)), 
// - word can be empty or up to 10000 terminal symbols (characters) long. 		
// -- References -- 
//  [1] Jay Earley. An Efficient Context-Free Parsing Algorithm. Communications of the ACM, 1970. 
//  [2] John Aycock and Nigel Horspool. Practical Earley Parsing. Computer Journal, 2002. 
// 

import java.io.BufferedReader;
import java.io.FileReader;
import java.util.*;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Scanner;
// Single production 
// Assume nonterminal is always a single character from {A,B,...,Z}, and terminal is always a string over {a,b,...,z} 
// prodHead -> prodRhs 
class Production {
	public Character prodHead; // head
	public Character[] prodRhs; // right hand side

	// Constructor
	public Production(Character prodHead, Character[] prodRhs) {
		this.prodHead = prodHead;
		this.prodRhs = prodRhs;
	}

	public Production(String prodHead, String prodRhs) {
		//assert(prodHead.length() == 1);
		this.prodHead = prodHead.charAt(0);
		this.prodRhs = toCharacterArray(prodRhs.toCharArray());
	}

	public boolean equals(Object o) {
		if (this == o) {
			return true;
		} else if (!(o instanceof Production)) {
			return false;
		} else {
			Production p = (Production) o;
			return prodHead.equals(p.prodHead) && Arrays.equals(prodRhs, p.prodRhs);
		}
	}

	// Helper
	private static Character[] toCharacterArray(char[] array) {
		Character[] chArray = new Character[array.length];
		for (int i = 0; i < array.length; ++i) {
			chArray[i] = array[i];
		}
		return chArray;
	}
}

// Let G = (V, T, P, S) be a context-free grammar 
class Grammar {
	public ArrayList<Production> productions; // P

	// Constructor
	public Grammar() {
		productions = new ArrayList<Production>();
	}

	public Grammar(ArrayList<Production> productions) {
		this.productions = productions;
	}

	public boolean addProduction(Production prod) {
		return !productions.contains(prod) && productions.add(prod);
	}

	public boolean addProduction(Character prodHead, Character[] prodRhs) {
		return addProduction(new Production(prodHead, prodRhs));
	}

	public boolean addProduction(String prodHead, String prodRhs) {
		return addProduction(new Production(prodHead, prodRhs));
	}

	// Compute the set of nullable nonterminals: { A in V | A =>* eps }
	// I decided to go with a simple fixed-point algorithm
	public Set<Character> getNullable() {
		Set<Character> nullSet = new TreeSet<Character>();
		// find the ``base'' symbols --- all A in V such that A -> eps is in P
		for (Production p : productions) {
			if (p.prodRhs[0] == '~') {
				nullSet.add(p.prodHead);
			}
		}
		if (nullSet.size() != 0) {
			boolean isNullable = true;
			int crrSize = nullSet.size();
			do {
				crrSize = nullSet.size();
				for (Production p : productions) {
					isNullable = true;
					for (Character c : p.prodRhs) {
						if (c.isLowerCase(c) && c.isLetter(c) || !nullSet.contains(c)) {
							isNullable = false;
							break;
						}
					}
					if (isNullable) {
						nullSet.add(p.prodHead);
					}
				}
			} while (crrSize != nullSet.size());
		}
		return nullSet;
	}
}

// State 
class State {
	public Production prod;
	public int rhsIdx;
	public int prevSet;

	// Constructor
	public State(Production prod, int rhsIdx, int prevSet) {
		this.prod = prod; // production
		this.rhsIdx = rhsIdx; // position of the dot on the right-hand-side of the production
		this.prevSet = prevSet;
	}

	public boolean equals(Object o) {
		if (this == o) {
			return true;
		} else if (!(o instanceof State)) {
			return false;
		} else {
			State s = (State) o;
			// System.out.println("[DEBUG] " + prod.equals(s.prod));
			return rhsIdx == s.rhsIdx && prevSet == s.prevSet && prod.equals(s.prod);
		}
	}
}

public class CFG {
	private Grammar g;
	private ArrayList<LinkedList<State>> stateSets;

	public CFG() {
		g = new Grammar();
		stateSets = new ArrayList<LinkedList<State>>();
	}

	// helper methods
	private boolean isNonterminal(Character c) {
		return Character.isUpperCase(c) || c.equals('@');
	}

	// prints state set contents

	private void print() {
		for (int idx = 0; idx < stateSets.size(); ++idx) {
			System.out.println("------ State set " + idx + " -----------");
			System.out.println("--LHS------RHS-----DotIndex---PrevSet");
			for (State s : stateSets.get(idx)) {
				String rhs = Arrays.toString(s.prod.prodRhs).replaceAll(", ", "").substring(1,
						s.prod.prodRhs.length + 1);
				System.out.println(s.prod.prodHead + "     ->     " + rhs + ",         " + s.rhsIdx + " ;  " + s.prevSet);
			}
		}
	}

	// If production (P, j) is in S_i and x_{i+1}= current terminal, then add P with
	// rhsIdx+1 to S_{i+1}
	private void scanner(State state, int crrIdx) {
		State newState = new State(state.prod, state.rhsIdx + 1, state.prevSet);
		if (!stateSets.get(crrIdx + 1).contains(newState)) {
			stateSets.get(crrIdx + 1).add(newState);
		}
	}

	// We use the predictor from [2]; it nicely handles $\varepsilon$-productions
	// For [A -> alpha o E beta, i], it adds [E -> o gamma, j] for all productions
	// in S_i
	// with E on the left-hand side
	private void predictor(State state, int crrIdx, Set<Character> nullableVars) {
		Character B = state.prod.prodRhs[state.rhsIdx];
		for (Production p : g.productions) {
			if (p.prodHead.equals(B)) {
				State newState = new State(p, 0, crrIdx);
				if (!stateSets.get(crrIdx).contains(newState)) {
					stateSets.get(crrIdx).add(newState);
				}
			}
		}
		// Need this to handle $\varepsilon$-productions [2]
		if (nullableVars.contains(B)) { // B is nullable, i.e., B =>* eps
			State newState = new State(state.prod, state.rhsIdx + 1, state.prevSet);
			if (!stateSets.get(crrIdx).contains(newState)) {
				stateSets.get(crrIdx).add(newState);
			}
		}
	}

	private void completer(State state, int crrIdx) {
		int j = state.prevSet;
		LinkedList<State> stateSet = stateSets.get(j);
		for (int i = 0; i < stateSet.size(); ++i) {
			State s = stateSet.get(i);
			if (s.rhsIdx < s.prod.prodRhs.length && s.prod.prodRhs[s.rhsIdx].equals(state.prod.prodHead)) {
				State newState = new State(s.prod, s.rhsIdx + 1, s.prevSet);
				if (!stateSets.get(crrIdx).contains(newState)) {
					stateSets.get(crrIdx).add(newState);
				}
			}
		}
	}

	private void initialize(int n) {
		// add the initial state set S_0
		Production newProd = new Production("@", "E");
		LinkedList<State> initState = new LinkedList<State>();
		initState.add(new State(newProd, 0, 0));
		stateSets.add(initState);

		for (int i = 0; i < n; ++i) {
			stateSets.add(new LinkedList<State>());
		}
	}

	private void process(int i, Character a, Set<Character> nullableVars) {
		LinkedList<State> stateSet = stateSets.get(i);
		int crrSize = 0;
		do {
			crrSize = stateSet.size();
			// iterate over the states from the current state set
			for (int j = 0; j < crrSize; ++j) {
				State state = stateSet.get(j);
				// apply either scanner, predictor, or completer
				if (state.rhsIdx == state.prod.prodRhs.length) {
					completer(state, i);
				} else {
					if (isNonterminal(state.prod.prodRhs[state.rhsIdx])) {
						predictor(state, i, nullableVars);
					} else if (state.prod.prodRhs[state.rhsIdx].equals(a)) {
						scanner(state, i);
					} // else Nothing left to do
				}
			}
		} while (crrSize != stateSet.size());
	}

	public boolean solve(String[] grammar, String word) {
		// load the grammar
		for (String s : grammar) {
			// System.out.println(s);
			Character prodHead = s.charAt(0);
			for (String rhs : s.split("->")[1].split("\\|")) {
				g.addProduction(s, rhs);
			}
		}
		// compute nullable symbols
		Set<Character> nullableVars = g.getNullable();
		// run the earley recognizer
		initialize(word.length());
		for (int i = 0; i < word.length(); ++i) {
			int crrSet = i + 1; // set index
			Character a = word.charAt(i);
			// Initialize the set S_{i+1} by applying the three operations to S_i until S_i
			// stops changing
			process(i, a, nullableVars);
		}
		process(word.length(), '/', nullableVars); // character '/' is never in T

		State finalState = new State(new Production("@", "E"), 1, 0);
		LinkedList<State> lastStateSet = stateSets.get(word.length());
		print();
		for (State s : lastStateSet) {
			if (s.equals(finalState)) {

				return true;
			}

		}
		return false;
	}

	public static boolean wordInGrammar(String g, String w) {
		CFG ep = new CFG();
		return ep.solve(g.split(";"), w);
	}

	public static void main(String[] args) {
		try {
			FileReader fileReader = new FileReader("CFG.txt");
			String line;
			String grammar="";
			BufferedReader br = new BufferedReader(fileReader);
			
			while ((line = br.readLine()) != null) {// read lines
				grammar += line;
				//System.out.println(grammar+"  1");
				grammar += ";";
				//System.out.println(grammar + " 2");
			}
			br.close();
			Scanner input = new Scanner(System.in);
			System.out.println("Enter string");
			String string = input.next();
			if (wordInGrammar(grammar, string)) {
				System.out.println("This string belongs to your language");
			} else {
				System.out.println("This string does not belong to your language");
			}

		} catch (Exception e) {
			System.out.println(e);
		}

	}
}

