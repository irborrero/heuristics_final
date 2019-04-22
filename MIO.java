import java.io.*;
import java.util.Scanner;
import org.jacop.core.BooleanVar;
import org.jacop.core.Store;
import org.jacop.jasat.utils.structures.IntVec;
import org.jacop.satwrapper.SatWrapper;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import java.util.ArrayList;

//prueba guardado
public class MIO {

	public static void main(String[] args) throws FileNotFoundException {
		// TODO Auto-generated method stub


		//Reading input file
		String file = "";
		Scanner input = new Scanner(new File("data.txt"));
		while(input.hasNext()) {
			 String i = input.next();
	         file += i;
		}
		
		input.close();
		
		System.out.println("Entrada: "+file);
		System.out.println();
		
		//SAT problem
		Store store = new Store();
		SatWrapper satWrapper = new SatWrapper(); 
		store.impose(satWrapper);				
	
		
		//Creating BooleanVar matrix
		int rows= Character.getNumericValue(file.charAt(0)); //streets
		int columns= Character.getNumericValue(file.charAt(1)); //number of cars in each street
		System.out.println("Parking streets: "+rows);
		System.out.println("Number of cars in each street: "+columns);
		
		System.out.println();
			BooleanVar [][] empty= new BooleanVar [rows][columns]; //indicates if a parking space is empty
			BooleanVar [][] bigger= new BooleanVar [rows][columns]; //indicates if the front car is going to stay longer
			BooleanVar [][] smaller= new BooleanVar [rows][columns]; //indicates if the front parking space has a car that is going to stay less time
			BooleanVar [][] equal= new BooleanVar [rows][columns];
			BooleanVar [][] time= new BooleanVar [rows][columns];
			BooleanVar [][] left= new BooleanVar [rows][columns];
			BooleanVar [][] right= new BooleanVar [rows][columns];
		
		//Creating literal matrix associated with BooleanVar matrix
			int [][] empty_literal= new int [rows][columns]; //literal that indicates if a parking space is empty
			int [][] bigger_literal= new int [rows][columns]; //literal that indicates if a parking space is empty
			int [][] smaller_literal= new int [rows][columns]; //literal that indicates if the front parking space has a car that is going to stay less time
			int [][] equal_literal= new int [rows][columns]; //literal that indicates if the front parking space has a car that may stay the same time
			int [][] time_literal= new int [rows][columns];
			int [][] left_literal= new int [rows][columns];
			int [][] right_literal= new int [rows][columns];
			
			
		//ArrrayList with all variables
		ArrayList<BooleanVar> variables=new ArrayList<BooleanVar>();			
 		BooleanVar[] allVariables = new BooleanVar[variables.size()];	
 		allVariables = variables.toArray(allVariables);
 		
 		//Initializing matrix
 				for(int i = 0; i<rows; i++) {
 					for(int j = 0; j<columns; j++) {
 						
 						//Creating boolean variables 
 						empty[i][j] = new BooleanVar(store, "Empty park car:"+" "+i+" "+j); 
 						bigger[i][j] = new BooleanVar(store, "Front car is leaving later:"+" "+i+" "+j); 
 						smaller[i][j] = new BooleanVar(store, "Front car leaving eralier: "+" "+i+" "+j); 
 						equal[i][j] = new BooleanVar(store, "Delante misma categoría: "+" "+i+" "+j); 
 						time[i][j] = new BooleanVar(store, "Delante misma categoría- tiempo adecuado: "+" "+i+" "+j); 
 						left[i][j] = new BooleanVar(store, " < "); 
 						right[i][j] = new BooleanVar(store, " > ");
 						
 						//Registering boolean variables and adding them to ArrayList
 						variables.add(empty[i][j]);
 						satWrapper.register(empty[i][j]);
 						
 						variables.add(bigger[i][j]);
 						satWrapper.register(bigger[i][j]);
 						
 						variables.add(smaller[i][j]);
 						satWrapper.register(smaller[i][j]);
 						
 						variables.add(time[i][j]);
 						satWrapper.register(time[i][j]);
 						
 						variables.add(equal[i][j]);
 						satWrapper.register(equal[i][j]);
 						
 						variables.add(left[i][j]);
 						satWrapper.register(left[i][j]);
 						
 						variables.add(right[i][j]);
 						satWrapper.register(right[i][j]);
 						
 						//We obtain the non negated literals from the variables
 						empty_literal[i][j] = satWrapper.cpVarToBoolVar(empty[i][j], 1, true);
 						bigger_literal[i][j] = satWrapper.cpVarToBoolVar(bigger[i][j], 1, true);
 						smaller_literal[i][j] = satWrapper.cpVarToBoolVar(smaller[i][j], 1, true);
 						equal_literal[i][j] = satWrapper.cpVarToBoolVar(equal[i][j], 1, true);
 						time_literal[i][j] = satWrapper.cpVarToBoolVar(time[i][j], 1, true);
 						left_literal[i][j] = satWrapper.cpVarToBoolVar(left[i][j], 1, true);
 						right_literal[i][j] = satWrapper.cpVarToBoolVar(right[i][j], 1, true);
 						
 						}
 					}

 				//stocking variables on ArrralyList
 				allVariables = variables.toArray(allVariables);
 				
 			int position=2;	 
 			
 				for(int i = 0; i<rows; i++) {
 		 			for(int j = 0; j<columns; j++) {
 		 				
 		 				if(j == 0){
 		 					addClause(satWrapper, left_literal[i][j]);
 		 				}
 		 			
 		 				if(file.charAt(position) == '_') {
		 	 					addClause(satWrapper, empty_literal[i][j]);
		 	 					
		 	 				}
		 					
		 				if(file.charAt(position) != '_') {
		 	 					addClause(satWrapper, -empty_literal[i][j]);
		 	 				}
 		 				
 		 				if(j<columns-1) {
 		 					
 							if(file.charAt(position) > file.charAt(position + 2)){
 								addClause(satWrapper, -bigger_literal[i][j]);
 								addClause(satWrapper, -equal_literal[i][j]);
 								addClause(satWrapper, smaller_literal[i][j]);
 								
 							}
 							
 							if(file.charAt(position) < file.charAt(position + 2)){
 								addClause(satWrapper, bigger_literal[i][j]);
 								addClause(satWrapper, -equal_literal[i][j]);
 								addClause(satWrapper, -smaller_literal[i][j]);
 								
 							}
 							
 							if(file.charAt(position) == file.charAt(position + 2)){
 								addClause(satWrapper, -bigger_literal[i][j]);
 								addClause(satWrapper, equal_literal[i][j]);
 								addClause(satWrapper, -smaller_literal[i][j]);
 								
 							}
 							
 							if(file.charAt(position+1) > file.charAt(position + 3)) {
 								addClause(satWrapper, -time_literal[i][j]);
 								
 							}
 							
 							if(file.charAt(position+1) < file.charAt(position + 3)) {
 								addClause(satWrapper, time_literal[i][j]);
 								
 							}

 							if(file.charAt(position+1) == file.charAt(position + 3)) {
 								addClause(satWrapper, -time_literal[i][j]);
 								
 							}
 							
 		 				}else if(j == columns-1){ 
 		 					
 		 					addClause(satWrapper, -bigger_literal[i][j]);
 		 					addClause(satWrapper, -equal_literal[i][j]);
 		 					addClause(satWrapper, -smaller_literal[i][j]);
 		 					addClause(satWrapper, -time_literal[i][j]);
 		 					addClause(satWrapper, right_literal[i][j]);
 		 				}

 		 				position+=2;
 		 			}
 		 		}
 		 		
 	 
 		
 				for(int i = 0; i<rows; i++) {
 					for(int j = 1; j<columns-1; j++) {
 		 				
 			 		addClause(satWrapper, empty_literal[i][j-1], empty_literal[i][j], empty_literal[i][j+1], bigger_literal[i][j-1], smaller_literal[i][j], equal_literal[i][j], equal_literal[i][j-1]); /* (x v y) */
 			 		addClause(satWrapper, empty_literal[i][j-1], empty_literal[i][j], empty_literal[i][j+1], bigger_literal[i][j-1], smaller_literal[i][j], -time_literal[i][j], equal_literal[i][j-1]); /* (x v y) */
 			 		addClause(satWrapper, empty_literal[i][j-1], empty_literal[i][j], empty_literal[i][j+1], bigger_literal[i][j-1], smaller_literal[i][j], equal_literal[i][j], time_literal[i][j-1]); /* (x v y) */
 			 		addClause(satWrapper, empty_literal[i][j-1], empty_literal[i][j], empty_literal[i][j+1], bigger_literal[i][j-1], smaller_literal[i][j], -time_literal[i][j], time_literal[i][j-1]); /* (x v y) */			
 					
 			 		addClause(satWrapper, left_literal[i][j], -empty_literal[i][j-1]);
 			 		addClause(satWrapper, left_literal[i][j], -bigger_literal[i][j-1]);
 			 		addClause(satWrapper, left_literal[i][j], -equal_literal[i][j-1], -time_literal[i][j-1]);
 			 		
 			 		addClause(satWrapper, right_literal[i][j], -empty_literal[i][j+1]);
 			 		addClause(satWrapper, right_literal[i][j], -smaller_literal[i][j]);
 			 		addClause(satWrapper, right_literal[i][j], -empty_literal[i][j], time_literal[i][j]);
 			 		
 			 		addClause(satWrapper, right_literal[i][j], left_literal[i][j]);
 			 		
 			 		
 		 			}
 		 		}	
 				
 				//SOLVER
 				Search<BooleanVar> search = new DepthFirstSearch<BooleanVar>();
 				SelectChoicePoint<BooleanVar> select = new SimpleSelect<BooleanVar>(allVariables, new SmallestDomain<BooleanVar>(), new IndomainMin<BooleanVar>());
 				Boolean result = search.labeling(store, select);
 				
 				PrintWriter writer = new PrintWriter("output.txt");
 				

 				if (result) {
 					
 					System.out.println("Satisfacible");
 					for(int i = 0; i<rows; i++) {
 	 					for(int j = 0; j<columns; j++) {
 	 						
 	 						if(empty[i][j].dom().value() == 1){
 	 							writer.print(" _ ");
 	 						}
 	 						else if (left[i][j].dom().value() == 1){
		 						writer.print(left[i][j].id());
		 					}else if(right[i][j].dom().value() == 1){
		 						writer.print(right[i][j].id());
		 					}else{
		 						writer.print(" _ ");
		 					}
 	 					}writer.println();
 					}
 					
 				} else{
 					System.out.println("No Satisfacible");
 				}
 				writer.close();
 			}
	
	
	public static void addClause(SatWrapper satWrapper, int literal1){
		IntVec clause = new IntVec(satWrapper.pool);
		clause.add(literal1);
		satWrapper.addModelClause(clause.toArray());
	}
	
	public static void addClause(SatWrapper satWrapper, int literal1, int literal2){
		IntVec clause = new IntVec(satWrapper.pool);
		clause.add(literal1);
		clause.add(literal2);
		
		
		satWrapper.addModelClause(clause.toArray());
	}
	public static void addClause(SatWrapper satWrapper, int literal1, int literal2, int literal3){
		IntVec clause = new IntVec(satWrapper.pool);
		clause.add(literal1);
		clause.add(literal2);
		clause.add(literal3);
		
		satWrapper.addModelClause(clause.toArray());
	}
	
	public static void addClause(SatWrapper satWrapper, int literal1, int literal2, int literal3,int literal4, int literal5, int literal6, int literal7){
		IntVec clause = new IntVec(satWrapper.pool);
		clause.add(literal1);
		clause.add(literal2);
		clause.add(literal3);
		clause.add(literal4);
		clause.add(literal5);
		clause.add(literal6);
		clause.add(literal7);
		satWrapper.addModelClause(clause.toArray());
	}

}