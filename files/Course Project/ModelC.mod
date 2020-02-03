/*********************************************
 * OPL 12.6.0.0 Model
 * Author: oliveras
 * Creation Date: Apr 5, 2019 at 10:47:26 AM
 *********************************************/

 int nClasses = ...;
 int nOptions = ...;
 range O = 1..nOptions;
 range C = 1..nClasses;
 
 int carsOfClass[c in C] = ...;
 int classOption[c in C][o in O] = ...;              
 int m[o in O] = ...;
 int k[o in O] = ...;

 int nPositions; 
 execute {
 	nPositions = 0;
 	for (var c = 1; c <= nClasses; ++c)
 		nPositions += carsOfClass[c];
 }
 
 range P = 1..nPositions; 
 
 
 // IMPORTANT HINT!!!!!!
 // A position p in P is a possible starting point of a window for option o iff p + k[o] - 1 <= nPositions.
 // The window itself is [ p...(p+k[o]-1) ]
 
 dvar boolean pc[p in P][c in C];
 dvar boolean po[p in P][o in O];
 
 //dvar boolean zopt[p in P][o in O]; 
 //minimize sum(p in P, o in O) zopt[p][o];
  
 dvar int+ zOpt[o in O];
 minimize sum(i in O) (zOpt[i]);
 
 minimize 1;
  
 //sum (o in 1..(nOptions-2), c in C : classOption[c][o] == 1) (pc[p][c] + po[p][o]) <= 50; 
 
 subject to {
 	
 	//All positions have a car 
 	forall (p in P)
 	  sum(c in C) (pc[p][c]) == 1;
 	  
 	 //Cars of class is fulfilled
 	forall (c in C)
 	  sum(p in P) (pc[p][c]) == carsOfClass[c];
 	  
 	//Class options is fulfilled
	forall(p in P)
       forall(c in C)
           forall(o in O)
             (pc[p][c] == 1) => po[p][o] == classOption[c][o];
             
    //A
    forall(o in 1..nOptions)
      forall(p in 1..(nPositions - k[o] + 1))
        sum(i in p..p+k[o]-1) po[i][o] <= m[o];
         
 }

    //C
//	forall(o in O)
//	  forall(p in 1..(nPositions - k[o] + 1))
//             zopt[p][o] == (sum(i in p..p+k[o]-1) (po[i][o]) >= m[o]+1);
             
forall(o in O)
         zOpt[o] >= sum(p in 1..(nPositions - k[o] + 1)) !(sum(i in p..p+k[o]-1) (po[i][o]) <= m[o]);
}
// sum(j in 1..n) (pos[j] == i) = 1 per tot i entre 1..n <-- crea vector de posicions [1 3 2]
//
 execute {
  	var solution = new Array(1+nPositions);
 	write("SEQUENCE OF CLASSES: ");
 	for (var p = 1; p <= nPositions; ++p) {
 		var placed = 0; 
 		var cl;
 		for (var c = 1; c <= nClasses; ++c) if (pc[p][c] == 1) {++placed; cl = c;}
 		if (placed == 0) {writeln("ERROR: In position " + p + " there is no car"); stop();}
 		else if (placed > 1) {writeln("ERROR: In position " + p + " there is more than one car");stop();}
 		else {solution[p] = cl; write(cl + " ");} 		 
 	}
 	writeln();writeln();
 	for (var o = 1; o <= nOptions; ++o) {
 	 	
 		var violations = 0;
 	 	var solOpt = new Array(1+nPositions);
 		write("OPTION " + o + ":            ");
 		for (var p = 1; p <= nPositions; ++p) { 		 	 	
 			if (classOption[solution[p]][o] == 1) {write("X "); solOpt[p] = 1;}
 			else {write(". "); solOpt[p] = 0;}
        }    		
 		
 		for (p = 1; p + k[o] - 1 <= nPositions; ++p) {
 			placed = 0;
 			for (var pp = p; pp <= p + k[o] - 1; ++pp) {
 				if (solOpt[pp] == 1) ++placed;
  			} 			 			
 			if (placed > m[o]) { 			 			
 				if (violations == 0) write("\tViolations in windows: ");
 				++violations;
 				write("[" + p  + "..." + (p + k[o] - 1) + "] ");
   			} 				 			 		 		
 		}
 		
 		writeln();
 	} 		 		 	
 	
 }  