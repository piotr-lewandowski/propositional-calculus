Require Import Bool. 
Notation eqBool := eqb. 
Require Import String. 
Require Import List. 
Import ListNotations.

Notation propVar := string. 

Inductive proposition := 
  | var : propVar -> proposition
  | neg : proposition -> proposition 
  | conj : proposition -> proposition -> proposition
  | disj : proposition -> proposition -> proposition
  | impl : proposition -> proposition -> proposition
  | equiv : proposition -> proposition -> proposition. 

Inductive assignment := assign (s : propVar) (b : bool). 

Notation "# s" := (var s) (at level 1).
Notation "¬ p" := (neg p) (at level 2).
Notation "p ∧ r" := (conj p r) (at level 5, left associativity).
Notation "p ∨ r" := (disj p r) (at level 5, left associativity).
Notation "p → r" := (impl p r) (at level 10, left associativity).
Notation "p <=> r" := (equiv p r) (at level 10, left associativity).
Notation "s <- b" := (assign s b) (at level 0).  

(* retrieveBool is helper function for evaluating propositions, 
note that if there is no an suitable assignment in a given list
we simply return false *)
Fixpoint retrieveBool (s : propVar) (l : list assignment) : bool := 
  match l with
  | [] => false 
  | (t <- b) :: tail => if eqb s t then b else retrieveBool s tail 
  end. 

Fixpoint eval (p : proposition) (l : list assignment) : bool :=
  match p with
  | # s => retrieveBool s l 
  | ¬ r => negb (eval r l)
  | r ∨ q => orb (eval r l) (eval q l) 
  | r ∧ q => andb (eval r l) (eval q l)
  | r → q => orb (negb (eval r l)) (eval q l) 
  | r <=> q => eqBool (eval r l) (eval q l)
  end. 

Definition prop1 : proposition := ¬ # "x" ∨ (# "x" <=> # "y").
Eval compute in (eval prop1 ["x" <- true ; "y" <- false]). 
Eval compute in (eval prop1 ["x" <- true ; "y" <- true]). 
Eval compute in (eval prop1 ["x" <- false]). (* by default, "y" <- false *) 

Definition prop2 : proposition := (# "x" → # "y") ∧ # "z". 
Eval compute in (eval prop2 ["x" <- true ; "y" <- false ; "z" <- true]). 
Eval compute in (eval prop2 ["x" <- true ; "y" <- true ; "z" <- true]). 
Eval compute in (eval prop2 ["x" <- true ; "y" <- true ; "z" <- false]). 

Fixpoint contains (l : list propVar) (s : propVar) : bool := 
  match l with
  | [] => false 
  | t :: tail => if eqb s t then true else contains tail s 
  end.

Fixpoint removeDuplicates (l : list propVar) : list propVar := 
  match l with 
  | [] => [] 
  | s :: tail => if contains tail s then removeDuplicates tail 
                    else s :: (removeDuplicates tail) 
  end.  

Fixpoint getVars (p : proposition) : list propVar := 
  match p with 
  | # s => [ s ]
  | ¬ r => getVars r 
  | r ∨ q => (getVars r) ++ (getVars q) 
  | r ∧ q => (getVars r) ++ (getVars q)
  | r → q => (getVars r) ++ (getVars q)
  | r <=> q => (getVars r) ++ (getVars q)
  end.

(* function to generate all boolean sequences of length n *)
Fixpoint generateSequences (n : nat) : list (list bool) :=
  match n with
  | O => [[]]
  | S k => 
      let prevSequences := generateSequences k in
          map (fun seq => seq ++ [true]) prevSequences ++
          map (fun seq => seq ++ [false]) prevSequences
  end.

Fixpoint createAssignments (vars : list propVar) (values : list bool) : list assignment := 
  match vars , values with 
  | [] , _ => [] 
  | _ , [] => [] 
  | s :: tailVars , b :: tailValues => (s <- b) :: (createAssignments tailVars tailValues)
  end.

Fixpoint convertAssignmentsToFormula (l : list assignment) := 
  match l with 
  | [] => # "x" ∧ ¬ # "x"
  | (s <- b) :: [] => if b then # s else ¬ # s
  | (s <- b) :: tail => if b then # s ∧ (convertAssignmentsToFormula tail) 
                           else ¬ # s ∧ (convertAssignmentsToFormula tail)
  end. 

Definition convertToDNF (p : proposition) : proposition := 
  let vars := removeDuplicates (getVars p) in 
  let sequences := generateSequences (length vars) in 
  let assignments := map (fun seq => createAssignments vars seq) sequences in  
  let chosenRowsInTruthTable := filter (fun seq => eval p seq) assignments in 
  let formulas := map (fun row => convertAssignmentsToFormula row) chosenRowsInTruthTable in 
  match (head formulas) with 
  | None => # "x" ∧ ¬ # "x"
  | Some formula => fold_right (fun r q => r ∨ q) formula (tail formulas)
  end.

Fixpoint negateProposition (p : proposition) : proposition := 
  match p with 
  | # s => ¬ # s 
  | ¬ r => r  
  | r ∨ q => (negateProposition r) ∧ (negateProposition q) 
  | r ∧ q => (negateProposition r) ∨ (negateProposition q) 
  | r → q => r ∧ (negateProposition q) 
  | r <=> q => (r ∧ (negateProposition q)) ∨ (q ∧ (negateProposition r))
  end.

Definition convertToCNF (p : proposition) : proposition := 
  negateProposition (convertToDNF (¬ p)).

Definition prop3 : proposition := ¬ (# "x" ∧ # "y") <=> (¬ (¬ # "z" ∧ (# "x" <=> ¬ # "y"))).
Eval compute in (convertToCNF prop3). 
