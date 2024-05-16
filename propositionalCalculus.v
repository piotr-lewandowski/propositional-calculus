Require Import Bool. 
Notation eqBool := eqb. 
Require Import String. 
Require Import List. 
Import ListNotations.
Require Import Lia.

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
note that if there is no suitable assignment in a given list
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

Inductive scheffer :=
  | scheffer_var : propVar -> scheffer
  | scheffer_functor: scheffer -> scheffer -> scheffer.
  
Notation "$ s" := (scheffer_var s) (at level 1).
Notation "p // r" := (scheffer_functor p r) (at level 5, left associativity).
  
Fixpoint evalS (s : scheffer) (l : list assignment): bool :=
  match s with
  | $ s => retrieveBool s l
  | p // r => negb (andb (evalS p l) (evalS r l))
  end.
  
Definition negS (r : scheffer) : scheffer := r // r.
Definition andS (r q : scheffer) : scheffer := (q // r) // (q // r).
Definition orS (r q : scheffer) : scheffer := negS (andS (negS r) (negS q)).
Definition implS (r q : scheffer) : scheffer := orS (negS r) q.
Definition equivS (r q : scheffer) : scheffer := andS (implS r q) (implS q r).
  
Fixpoint convertToScheffer (p : proposition) : scheffer :=
  match p with
  | # s => $ s
  | ¬ r => negS (convertToScheffer r)
  | r ∨ q => let rs := convertToScheffer r in let qs := convertToScheffer q in orS rs qs
  | r ∧ q => let rs := convertToScheffer r in let qs := convertToScheffer q in andS rs qs
  | r → q => let rs := convertToScheffer r in let qs := convertToScheffer q in implS rs qs
  | r <=> q => let rs := convertToScheffer r in let qs := convertToScheffer q in equivS rs qs
  end.
  
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
  auto.
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

Inductive peirce :=
  | peirce_var : propVar -> peirce
  | peirce_arrow: peirce -> peirce -> peirce.
  
Notation "% s" := (peirce_var s) (at level 1).
Notation "p \\ r" := (peirce_arrow p r) (at level 5, left associativity).
  
Fixpoint evalP (s : peirce) (l : list assignment): bool :=
  match s with
  | % s => retrieveBool s l
  | p \\ r => negb (orb (evalP p l) (evalP r l))
  end.
  
Definition negP (r : peirce) : peirce := r \\ r.
Definition schefferP (r q : peirce) : peirce := negP ((negP r) \\ (negP q)).
  
Fixpoint convertToPeirce (p : scheffer) : peirce :=
  match p with
  | $ s => % s
  | r // q => schefferP (convertToPeirce r) (convertToPeirce q)
  end.
  
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
  
Theorem peirce_universality : forall p : proposition, exists s : scheffer, forall l : list assignment, evalS s l = eval p l.