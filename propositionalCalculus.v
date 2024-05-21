Require Import Bool. 
Notation eqBool := eqb. 
Require Import String. 
Require Import List. 
Import ListNotations.

(* Defining a type alias for proposition variables, which are represented as strings *)
Notation propVar := string. 

(* Definition of basic logical operators *) 
Inductive proposition := 
  | var : propVar -> proposition
  | neg : proposition -> proposition 
  | conj : proposition -> proposition -> proposition
  | disj : proposition -> proposition -> proposition
  | impl : proposition -> proposition -> proposition
  | equiv : proposition -> proposition -> proposition. 

(* Defining a type for assignment of boolean values to proposition variables *)
Inductive assignment := assign (s : propVar) (b : bool). 

(* Notations for creating propositions more easily *)
Notation "# s" := (var s) (at level 1).
Notation "¬ p" := (neg p) (at level 2).
Notation "p ∧ r" := (conj p r) (at level 5, left associativity).
Notation "p ∨ r" := (disj p r) (at level 5, left associativity).
Notation "p → r" := (impl p r) (at level 10, left associativity).
Notation "p <=> r" := (equiv p r) (at level 10, left associativity).
Notation "s <- b" := (assign s b) (at level 0).  

(* Helper function for evaluating propositions, 
note that if there is no suitable assignment in a given list
we simply return false *)
Fixpoint retrieveBool (s : propVar) (l : list assignment) : bool := 
  match l with
  | [] => false 
  | (t <- b) :: tail => if eqb s t then b else retrieveBool s tail 
  end. 

(* Function for evaluating a proposition with given a list of assignments *)
Fixpoint eval (p : proposition) (l : list assignment) : bool :=
  match p with
  | # s => retrieveBool s l 
  | ¬ r => negb (eval r l)
  | r ∨ q => orb (eval r l) (eval q l) 
  | r ∧ q => andb (eval r l) (eval q l)
  | r → q => orb (negb (eval r l)) (eval q l) 
  | r <=> q => eqBool (eval r l) (eval q l)
  end. 

(* Examples of propositions and their evaluations *)
Definition prop1 : proposition := ¬ # "x" ∨ (# "x" <=> # "y").
Eval compute in (eval prop1 ["x" <- true ; "y" <- false]). 
Eval compute in (eval prop1 ["x" <- true ; "y" <- true]). 
Eval compute in (eval prop1 ["x" <- false]). (* by default, "y" <- false *) 

Definition prop2 : proposition := (# "x" → # "y") ∧ ¬ # "z". 
Eval compute in (eval prop2 ["x" <- true ; "y" <- false ; "z" <- true]). 
Eval compute in (eval prop2 ["x" <- true ; "y" <- true ; "z" <- true]). 
Eval compute in (eval prop2 ["x" <- true ; "y" <- true ; "z" <- false]). 

(* Function to check if a list contains a specific proposition variable *)
Fixpoint contains (l : list propVar) (s : propVar) : bool := 
  match l with
  | [] => false 
  | t :: tail => if eqb s t then true else contains tail s 
  end.

(* Function to remove duplicates from a list of proposition variables *)
Fixpoint removeDuplicates (l : list propVar) : list propVar := 
  match l with 
  | [] => [] 
  | s :: tail => if contains tail s then removeDuplicates tail 
                    else s :: (removeDuplicates tail) 
  end.  

(* Function to get all proposition variables used in a proposition *)
Fixpoint getVars (p : proposition) : list propVar := 
  match p with 
  | # s => [ s ]
  | ¬ r => getVars r 
  | r ∨ q => (getVars r) ++ (getVars q) 
  | r ∧ q => (getVars r) ++ (getVars q)
  | r → q => (getVars r) ++ (getVars q)
  | r <=> q => (getVars r) ++ (getVars q)
  end.

(* Function to generate all boolean sequences of a given length *)
Fixpoint generateSequences (n : nat) : list (list bool) :=
  match n with
  | O => [[]]
  | S k => 
      let prevSequences := generateSequences k in
          map (fun seq => seq ++ [true]) prevSequences ++
          map (fun seq => seq ++ [false]) prevSequences
  end.

(* Function to create assignments from lists of variables and values *)
Fixpoint createAssignments (vars : list propVar) (values : list bool) : list assignment := 
  match vars , values with 
  | [] , _ => [] 
  | _ , [] => [] 
  | s :: tailVars , b :: tailValues => (s <- b) :: (createAssignments tailVars tailValues)
  end.

(* Function to convert a list of assignments to a propositional formula, 
this function is needed for algorithm which converts formula to its Disjunctive Normal Form *)
Fixpoint convertAssignmentsToFormula (l : list assignment) := 
  match l with 
  | [] => # "x" ∧ ¬ # "x"
  | (s <- b) :: [] => if b then # s else ¬ # s
  | (s <- b) :: tail => if b then # s ∧ (convertAssignmentsToFormula tail) 
                           else ¬ # s ∧ (convertAssignmentsToFormula tail)
  end.

(* Function to convert a proposition to its Disjunctive Normal Form *)
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

(* Function to negate a proposition *)
Fixpoint negateProposition (p : proposition) : proposition := 
  match p with 
  | # s => ¬ # s 
  | ¬ r => r  
  | r ∨ q => (negateProposition r) ∧ (negateProposition q) 
  | r ∧ q => (negateProposition r) ∨ (negateProposition q) 
  | r → q => r ∧ (negateProposition q) 
  | r <=> q => (r ∧ (negateProposition q)) ∨ (q ∧ (negateProposition r))
  end.

(* Function to convert a proposition to its Conjunctive Normal Form *) 
Definition convertToCNF (p : proposition) : proposition := 
  negateProposition (convertToDNF (¬ p)).

(* Example proposition and its conversion to CNF *)
Definition prop3 : proposition := ¬ (# "x" ∧ # "y") <=> (¬ (¬ # "z" ∧ (# "x" <=> ¬ # "y"))).
Eval compute in (convertToCNF prop3).

(* Definition of a new type for propositions using the Scheffer stroke operator *)
Inductive scheffer :=
  | scheffer_var : propVar -> scheffer
  | scheffer_functor: scheffer -> scheffer -> scheffer.

(* Notations for creating Scheffer propositions more easily *)
Notation "$ s" := (scheffer_var s) (at level 1).
Notation "p // r" := (scheffer_functor p r) (at level 5, left associativity).

(* Function for evaluating Scheffer propositions *)
Fixpoint evalS (s : scheffer) (l : list assignment): bool :=
  match s with
  | $ s => retrieveBool s l
  | p // r => negb (andb (evalS p l) (evalS r l))
  end.
  
(* Definition of basic logical operators using the Scheffer stroke *)
Definition negS (r : scheffer) : scheffer := r // r.
Definition andS (r q : scheffer) : scheffer := (q // r) // (q // r).
Definition orS (r q : scheffer) : scheffer := negS (andS (negS r) (negS q)).
Definition implS (r q : scheffer) : scheffer := orS (negS r) q.
Definition equivS (r q : scheffer) : scheffer := andS (implS r q) (implS q r).

(* Function to convert a proposition to a Scheffer proposition *)
Fixpoint convertPropToScheffer (p : proposition) : scheffer :=
  match p with
  | # s => $ s
  | ¬ r => negS (convertPropToScheffer r)
  | r ∨ q => let rs := convertPropToScheffer r in let qs := convertPropToScheffer q in orS rs qs
  | r ∧ q => let rs := convertPropToScheffer r in let qs := convertPropToScheffer q in andS rs qs
  | r → q => let rs := convertPropToScheffer r in let qs := convertPropToScheffer q in implS rs qs
  | r <=> q => let rs := convertPropToScheffer r in let qs := convertPropToScheffer q in equivS rs qs
  end.

(* Theorem stating the universality of the Scheffer's stroke *)
Theorem scheffer_universality : forall p : proposition, exists s : scheffer, forall l : list assignment, evalS s l = eval p l.
Proof.
  intros.
  induction p.
  (* constants *)
  exists ($ s).
  trivial.
  (* negation *)
  destruct IHp.
  exists (negS x).
  intro l.
  simpl.
  rewrite (H l).
  destruct (eval p l).
  trivial.
  trivial.
  (* conjunction *)
  destruct IHp1, IHp2.
  exists (andS x x0).
  intro l.
  simpl.
  rewrite (H l).
  rewrite (H0 l).
  destruct (eval p1 l), (eval p2 l).
  trivial.
  trivial.
  trivial.
  trivial.
  (* disjunction *)
  destruct IHp1, IHp2.
  exists (orS x x0).
  intro l.
  simpl.
  rewrite (H l).
  rewrite (H0 l).
  destruct (eval p1 l), (eval p2 l).
  trivial.
  trivial.
  trivial.
  trivial.
  (* implication *)
  destruct IHp1, IHp2.
  exists (implS x x0).
  intro l.
  simpl.
  rewrite (H l).
  rewrite (H0 l).
  destruct (eval p1 l), (eval p2 l).
  trivial.
  trivial.
  trivial.
  trivial.
  (* equivalence *)
  destruct IHp1, IHp2.
  exists (equivS x x0).
  intro l.
  simpl.
  rewrite (H l).
  rewrite (H0 l).
  destruct (eval p1 l), (eval p2 l).
  trivial.
  trivial.
  trivial.
  trivial.
Qed.

(* Definition of a new type for propositions using Peirce's arrow operator *)
Inductive peirce :=
  | peirce_var : propVar -> peirce
  | peirce_arrow: peirce -> peirce -> peirce.

(* Notations for creating Peirce propositions more easily *)
Notation "% s" := (peirce_var s) (at level 1).
Notation "p \\ r" := (peirce_arrow p r) (at level 5, left associativity).

(* Function for evaluating Peirce propositions *)
Fixpoint evalP (s : peirce) (l : list assignment): bool :=
  match s with
  | % s => retrieveBool s l
  | p \\ r => negb (orb (evalP p l) (evalP r l))
  end.

(* Definition of logical operators using Peirce's arrow *)
Definition negP (r : peirce) : peirce := r \\ r.
Definition schefferP (r q : peirce) : peirce := negP ((negP r) \\ (negP q)).
Definition orP (r q : peirce) : peirce := (q \\ r) \\ (q \\ r).
Definition andP (r q : peirce) : peirce := negP (orP (negP r) (negP q)).
Definition implP (r q : peirce) : peirce := orP (negP r) q.
Definition equivP (r q : peirce) : peirce := andP (implP r q) (implP q r).

(* Function to convert a Scheffer proposition to a Peirce proposition *)
Fixpoint convertSchefferToPeirce (p : scheffer) : peirce :=
  match p with
  | $ s => % s
  | r // q => schefferP (convertSchefferToPeirce r) (convertSchefferToPeirce q)
  end.

(* Theorem stating the equivalence of Peirce's arrow and Scheffer's stroke *)
Theorem peirce_scheffer_equivalence : forall s : scheffer, exists p : peirce, forall l : list assignment, evalS s l = evalP p l.
Proof.
  intros.
  induction s.
  (* constant *)
  exists (% s).
  trivial.
  (* scheffer *)
  destruct IHs1, IHs2.
  exists (schefferP x x0).
  intro l.
  simpl.
  rewrite (H l).
  rewrite (H0 l).
  destruct (evalP x l), (evalP x0 l).
  trivial.
  trivial.
  trivial.
  trivial.
Qed.

(* Function to convert a proposition to a Peirce proposition *)
Fixpoint convertPropToPeirce (p : proposition) : peirce := 
  match p with
  | # s => % s
  | ¬ r => negP (convertPropToPeirce r)
  | r ∨ q => let rr := convertPropToPeirce r in let qr := convertPropToPeirce q in orP rr qr
  | r ∧ q => let rr := convertPropToPeirce r in let qr := convertPropToPeirce q in andP rr qr
  | r → q => let rr := convertPropToPeirce r in let qr := convertPropToPeirce q in implP rr qr
  | r <=> q => let rr := convertPropToPeirce r in let qr := convertPropToPeirce q in equivP rr qr
  end.

(* Theorem stating the universality of Peirce's arrow,
we could prove this theorem in a similar way as we proved Scheffer's stroke universality, 
but we can also use two previous theorems instead *)  
Theorem peirce_universality : forall p : proposition, exists r : peirce, forall l : list assignment, evalP r l = eval p l.
Proof. 
  intros. 
  destruct (scheffer_universality p).
  destruct (peirce_scheffer_equivalence x). 
  exists x0. 
  intro l. 
  rewrite <- (H0 l). 
  rewrite (H l).
  trivial. 
Qed.
