(** * Imp: Simple Imperative Programs *)

(**

As programmers, we constantly define _abstractions_, be it through
full-blown programming languages, domain-specific languages or
APIs. The role of an abstraction is to hide operational details behind
an (hopefully) coherent interface.

In this lecture, we study how such interfaces can be mathematically
described in the Coq theorem prover. By mechanizing the _semantics_ of
an abstraction, we can experiment with its definitions and, if needs
be, actually prove its overall coherence. We can also effectively
implement these abstractions within Coq itself, thus providing a
certified, reference implementation. In this context, proofs replace
unit tests, thus relieving the programmer from implementing and
maintaining somewhat useless code.

 *)


(**

This file is a trimmed down, re-contextualized version of Pierce et
al. eponymous #<a
href="https://www.cis.upenn.edu/~bcpierce/sf/current/Imp.html">chapter</a>#
in the Software Foundations textbook.

 *)

(** In this file, we study a _simple imperative programming language_
    called Imp, embodying a tiny core fragment of conventional
    mainstream languages such as C and Java.  Here is a familiar
    mathematical function written in Imp.  

     Z ::= X;;
     Y ::= 1;;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END
*)

(** This file looks at how to define the _syntax_ and _semantics_
    of Imp. *)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.


(* ################################################################# *)
(** * Arithmetic and Boolean Expressions *)

(** We'll present Imp in three parts: first a core language of
    _arithmetic and boolean expressions_, then an extension of these
    expressions with _variables_, and finally a language of _commands_
    including assignment, conditions, sequencing, and loops. *)

(* ================================================================= *)
(** ** Syntax *)

Module AExp.

(** These two definitions specify the _abstract syntax_ of
    arithmetic and boolean expressions. *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(** For comparison, here's a conventional BNF (Backus-Naur Form)
    grammar defining the same abstract syntax:

    a ::= nat
        | a + a
        | a - a
        | a * a

    b ::= true
        | false
        | a = a
        | a <= a
        | not b
        | b and b
*)

(** Compared to the Coq version above...

       - The BNF is more informal -- for example, it gives some
         suggestions about the surface syntax of expressions (like the
         fact that the addition operation is written [+] and is an
         infix symbol) while leaving other aspects of lexical analysis
         and parsing (like the relative precedence of [+], [-], and
         [*], the use of parens to explicitly group subexpressions,
         etc.) unspecified.  Some additional information (and human
         intelligence) would be required to turn this description into
         a formal definition, for example when implementing a
         compiler.

         The Coq version consistently omits all this information and
         concentrates on the abstract syntax only.

       - On the other hand, the BNF version is lighter and easier to
         read.  Its informality makes it flexible, which is a huge
         advantage in situations like discussions at the blackboard,
         where conveying general ideas is more important than getting
         every detail nailed down precisely.

         Indeed, there are dozens of BNF-like notations and people
         switch freely among them, usually without bothering to say
         which form of BNF they're using because there is no need to:
         a rough-and-ready informal understanding is all that's
         important. 

    It's good to be comfortable with both sorts of notations:
    informal ones for communicating between humans and formal ones for
    carrying out implementations and proofs. *)

(* ================================================================= *)
(** ** Evaluation *)

(** _Evaluating_ an arithmetic expression produces a number. *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(** Similarly, evaluating a boolean expression yields a boolean. *)

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2   => leb (aeval a1) (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* ================================================================= *)
(** ** Optimization *)

(** We haven't defined very much yet, but we can already get
    some mileage out of the definitions.  Suppose we define a function
    that takes an arithmetic expression and slightly simplifies it,
    changing every occurrence of [0+e] (i.e., [(APlus (ANum 0) e])
    into just [e]. *)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

(** To make sure our optimization is doing the right thing we
    can test it on some examples and see if the output looks OK. *)

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

(** But if we want to be sure the optimization is correct --
    i.e., that evaluating an optimized expression gives the same
    result as the original -- we should prove it. *)

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1.
    + (* a1 = ANum n *) destruct n.
      * (* n = 0 *)  simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.


(** This proof can still be improved: the first case (for [a = ANum
    n]) is very trivial -- even more trivial than the cases that we
    said simply followed from the IH -- yet we have chosen to write it
    out in full.  It would be better and clearer to drop it and just
    say, at the top, "Most cases are either immediate or direct from
    the IH.  The only interesting case is the one for [APlus]..."  We
    can make the same improvement in our formal proof too.  Here's how
    it looks: *)

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

(** **** Exercise: 3 stars (optimize_0plus_b)  *)
(** Since the [optimize_0plus] transformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function which performs that transformation on [bexp]s, and prove
    it is sound. *)

Fixpoint optimize_0plus_b (b : bexp) : bexp 
  (* REPLACE THIS LINE WITH   := _your_definition_ . *) . Admitted.


(** 
[[
Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
]]
*)


(** **** Exercise: 4 stars, optional (optimizer)  *)
(** _Design exercise_: The optimization implemented by our
    [optimize_0plus] function is only one of many possible
    optimizations on arithmetic and boolean expressions.  Write a more
    sophisticated optimizer and prove it correct. *)


(* ################################################################# *)
(** * Evaluation as a Relation *)

(** We have presented [aeval] and [beval] as functions defined by
    [Fixpoint]s.  Another way to think about evaluation -- one that we
    will see is often more flexible -- is as a _relation_ between
    expressions and their values.  This leads naturally to [Inductive]
    definitions like the following one for arithmetic expressions... *)

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum  : forall (n: nat),
      aevalR (ANum n) n
  | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

(** As is often the case with relations, we'll find it
    convenient to define infix notation for [aevalR].  We'll write [e
    \\ n] to mean that arithmetic expression [e] evaluates to value
    [n].  (This notation is one place where the limitation to ASCII
    symbols becomes a little bothersome.  The standard notation for
    the evaluation relation is a double down-arrow.  We'll typeset it
    like this in the HTML version of the notes and use a double slash
    as the closest approximation in [.v] files.)  *)

Notation "e '⇓' n"
         := (aevalR e n) 
            (at level 50, left associativity)
         : type_scope.

End aevalR_first_try.

(** In fact, Coq provides a way to use this notation in the definition
    of [aevalR] itself.  This avoids situations where we're working on
    a proof involving statements in the form [e \\ n] but we have to
    refer back to a definition written using the form [aevalR e n].

    We do this by first "reserving" the notation, then giving the
    definition together with a declaration of what the notation
    means. *)

Reserved Notation "e '⇓' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
  (*----------------*)
      (ANum n) ⇓ n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      e1 ⇓ n1 -> 
      e2 ⇓ n2 -> 
  (*--------------------------------*)
      (APlus e1 e2) ⇓ (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      e1 ⇓ n1 -> 
      e2 ⇓ n2 -> 
  (*--------------------------------*)
      (AMinus e1 e2) ⇓ (n1 - n2)
  | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat),
      e1 ⇓ n1 -> 
      e2 ⇓ n2 -> 
  (*--------------------------------*)
      (AMult e1 e2) ⇓ (n1 * n2)

  where "e '⇓' n" := (aevalR e n) : type_scope.

(* ================================================================= *)
(** ** Inference Rule Notation *)

(** In informal discussions, it is convenient to write the rules for
    [aevalR] and similar relations in the more readable graphical form
    of _inference rules_, where the premises above the line justify
    the conclusion below the line (we have already seen them in the
    Prop chapter). *)

(** For example, the constructor [E_APlus]...

      | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
      (*--------------------------------*)
          aevalR (APlus e1 e2) (n1 + n2)

    ...would be written like this as an inference rule:

                               e1 ⇓ n1
                               e2 ⇓ n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 ⇓ n1+n2
*)

(** Formally, there is nothing deep about inference rules: they
    are just implications.  You can read the rule name on the right as
    the name of the constructor and read each of the linebreaks
    between the premises above the line and the line itself as [->].
    All the variables mentioned in the rule ([e1], [n1], etc.) are
    implicitly bound by universal quantifiers at the beginning. (Such
    variables are often called _metavariables_ to distinguish them
    from the variables of the language we are defining.  At the
    moment, our arithmetic expressions don't include variables, but
    we'll soon be adding them.)  The whole collection of rules is
    understood as being wrapped in an [Inductive] declaration.  In
    informal prose, this is either elided or else indicated by saying
    something like "Let [aevalR] be the smallest relation closed under
    the following rules...". *)

(** For example, [⇓] is the smallest relation closed under these
    rules:

                             -----------                               (E_ANum)
                             ANum n ⇓ n

                               e1 ⇓ n1
                               e2 ⇓ n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 ⇓ n1+n2

                               e1 ⇓ n1
                               e2 ⇓ n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 ⇓ n1-n2

                               e1 ⇓ n1
                               e2 ⇓ n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 ⇓ n1*n2
*)

(* ================================================================= *)
(** ** Equivalence of the Definitions *)

(** It is straightforward to prove that the relational and functional
    definitions of evaluation agree, for all arithmetic expressions... *)

Theorem aeval_iff_aevalR : forall a n,
  (a ⇓ n) <-> aeval a = n.
Proof.
 split.
 - (* -> *)
   intros H.
   induction H; simpl.
   + (* E_ANum *)
     reflexivity.
   + (* E_APlus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMinus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMult *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
 - (* <- *)
   generalize dependent n.
   induction a;
      simpl; intros; subst.
   + (* ANum *)
     apply E_ANum.
   + (* APlus *)
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMinus *)
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMult *)
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.

(** We can make the proof quite a bit shorter by making more
    use of tacticals... *)

Theorem aeval_iff_aevalR' : forall a n,
  a ⇓ n <-> aeval a = n.
Proof.
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

(** **** Exercise: 3 stars  (bevalR)  *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)


End AExp.

(* ================================================================= *)
(** ** Computational vs. Relational Definitions *)

(** For the definitions of evaluation for arithmetic and boolean
    expressions, the choice of whether to use functional or relational
    definitions is mainly a matter of taste.  In general, Coq has
    somewhat better support for working with relations.  On the other
    hand, in some sense function definitions carry more information,
    because functions are by definition deterministic and defined on
    all arguments; for a relation we have to show these properties
    explicitly if we need them.  Functions also take advantage of
    Coq's computation mechanism.

    However, there are circumstances where relational definitions of
    evaluation are preferable to functional ones.  *)

Module aevalR_division.

(** For example, suppose that we wanted to extend the arithmetic
    operations by considering also a division operation:*)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ADiv : aexp -> aexp -> aexp.   (* <--- new *)

(** Extending the definition of [aeval] to handle this new operation
    would not be straightforward (what should we return as the result
    of [ADiv (ANum 5) (ANum 0)]?).  But extending [aevalR] is
    straightforward. *)

Reserved Notation "e '⇓' n"
                  (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),

  (*----------------*)
      (ANum n) ⇓ n

  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),

      a1 ⇓ n1 -> 
      a2 ⇓ n2 ->
  (*-----------------------------*)
      (APlus a1 a2) ⇓ (n1 + n2)

  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),

      a1 ⇓ n1 ->
      a2 ⇓ n2 -> 
  (*-----------------------------*)
      (AMinus a1 a2) ⇓ (n1 - n2)

  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),

      a1 ⇓ n1 ->
      a2 ⇓ n2 -> 
  (*-----------------------------*)
      (AMult a1 a2) ⇓ (n1 * n2)

  | E_ADiv :  forall (a1 a2: aexp) (n1 n2 n3: nat),

      a1 ⇓ n1 -> 
      a2 ⇓ n2 -> 
      n2 > 0 -> 
      mult n2 n3 = n1 -> 
  (*------------------------------------------*)
      (ADiv a1 a2) ⇓ n3

where "a '⇓' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.

(* ----------------------------------------------------------------- *)
(** *** Adding Nondeterminism *)

(** Suppose, instead, that we want to extend the arithmetic operations
    by a nondeterministic number generator [any] that, when evaluated,
    may yield any number.  (Note that this is not the same as making a
    _probabilistic_ choice among all possible numbers -- we're not
    specifying any particular distribution of results, but just saying
    what results are _possible_.) *)

Reserved Notation "e '⇓' n" (at level 50, left associativity).

Inductive aexp : Type :=
  | AAny  : aexp                   (* <--- NEW *)
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

(** Again, extending [aeval] would be tricky, since now evaluation is
    _not_ a deterministic function from expressions to numbers, but
    extending [aevalR] is no problem: *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any : forall (n:nat),

  (*-----------------------------*)
      AAny ⇓ n                 (* <--- new *)

  | E_ANum : forall (n:nat),

  (*-----------------------------*)
      (ANum n) ⇓ n

  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),

      a1 ⇓ n1 -> 
      a2 ⇓ n2 -> 
  (*-----------------------------*)
      (APlus a1 a2) ⇓ (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),

      a1 ⇓ n1 -> 
      a2 ⇓ n2 -> 
  (*-----------------------------*)
      (AMinus a1 a2) ⇓ (n1 - n2)
               
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),

      a1 ⇓ n1 -> 
      a2 ⇓ n2 ->
  (*-----------------------------*)
      (AMult a1 a2) ⇓ (n1 * n2)

where "a '⇓' n" := (aevalR a n) : type_scope.

End aevalR_extended.

(* ################################################################# *)
(** * Interlude: Total Maps *)


(** Maps (or dictionaries) are ubiquitous data structures, both in
    software construction generally and in the theory of programming
    languages in particular.

    Here, we'll define _total_ maps, which include a "default" element to be
    returned when a key being looked up doesn't exist. *)

(** * Identifiers *)

(** First, we need a type for the keys that we use to index into our
    maps.  For this purpose, we define a new inductive datatype [id]
    to serve as the "keys" of our partial maps. *)

Inductive id : Type :=
  | Id : nat -> id.

(** Internally, an [id] is just a number.  Introducing a separate type
    by wrapping each nat with the tag [Id] makes definitions more
    readable and gives us the flexibility to change representations
    later if we wish.

    We'll also need an equality test for [id]s: *)

Definition beq_id x1 x2 :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

(** **** Exercise: 1 star (beq_id_refl)  *)

(** Prove 

[[
  Theorem beq_id_refl : forall x, true = beq_id x x.
]]
*)


(** The following useful property of [beq_id] follows from an
    analogous lemma about numbers: *)

Theorem beq_id_true_iff : forall id1 id2 : id,
  beq_id id1 id2 = true <-> id1 = id2.
Proof.
   intros [n1] [n2].
   unfold beq_id.
   rewrite beq_nat_true_iff.
   split.
   - (* -> *) intros H. rewrite H. reflexivity.
   - (* <- *) intros H. inversion H. reflexivity.
Qed.

(** Similarly: *)

Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false. reflexivity. 
Qed.

(** This useful variant follows just by rewriting: *)

Theorem false_beq_id : forall x y : id,
   x <> y
   -> beq_id x y = false.
Proof.
  intros x y. rewrite beq_id_false_iff.
  intros H. apply H. 
Qed.

(* ################################################################# *)
(** * Total Maps *)

(** We define a type of _total maps_ that return a default value when
    we look up a key that is not present in the map. *)

Definition total_map (A:Type) := id -> A.

(** Intuitively, a total map over an element type [A] _is_ just a
    function that can be used to look up [id]s, yielding [A]s.

    The function [t_empty] yields an empty total map, given a default
    element; this map always returns the default element when applied
    to any id. *)

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

(** More interesting is the [update] function, which takes a map [m],
    a key [x], and a value [v] and returns a new map that takes [x] to
    [v] and takes every other key to whatever [m] does. *)

Definition t_update {A:Type} (m : total_map A)
                    (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.

(** This definition is a nice example of higher-order programming.
    The [t_update] function takes a _function_ [m] and yields a new
    function [fun x' => ...] that behaves like the desired map.

    For example, we can build a map taking [id]s to [bool]s, where [Id
    3] is mapped to [true] and every other key is mapped to [false],
    like this: *)

Definition examplemap :=
  t_update (t_update (t_empty false) (Id 1) false)
           (Id 3) true.

(** This completes the definition of total maps.  Note that we don't
    need to define a [find] operation because it is just function
    application! *)

Example update_example1 : examplemap (Id 0) = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap (Id 1) = false.
Proof. reflexivity. Qed.

Example update_example3 : examplemap (Id 2) = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap (Id 3) = true.
Proof. reflexivity. Qed.

(** We'll need several fundamental facts about how they behave.  Even
    if you don't work the following exercises, make sure you
    thoroughly understand the statements of the lemmas!  (Some of the
    proofs require the functional extensionality axiom.) *)

(** **** Exercise: 1 star, optional (t_apply_empty)  *)
(** First, the empty map returns its default element for all keys: 

[[
    Lemma t_apply_empty:  forall A x v, @t_empty A v x = v.
]]
*)



(** **** Exercise: 2 stars, optional (t_update_eq)  *)
(** Next, if we update a map [m] at a key [x] with a new value [v]
    and then look up [x] in the map resulting from the [update], we
    get back [v]: 
*)

Lemma t_update_eq : forall A (m: total_map A) x v,
    (t_update m x v) x = v.
Admitted.



(** **** Exercise: 2 stars, optional (t_update_neq)  *)
(** On the other hand, if we update a map [m] at a key [x1] and then
    look up a _different_ key [x2] in the resulting map, we get the
    same result that [m] would have given: 

[[
  Theorem t_update_neq : forall (X:Type) v x1 x2
                           (m : total_map X),
    x1 <> x2 ->
    (t_update m x1 v) x2 = m x2.
]]

*)


(** **** Exercise: 3 stars, optional (t_update_shadow)  *)
(** If we update a map [m] at a key [x] with a value [v1] and then
    update again with the same key [x] and another value [v2], the
    resulting map behaves the same (gives the same result when applied
    to any key) as the simpler map obtained by performing just
    the second [update] on [m]: 


[[
  Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
      t_update (t_update m x v1) x v2
    = t_update m x v2.
]]

*)


(** For the final two lemmas, we begin by proving a fundamental
    _reflection lemma_ relating the equality proposition on [id]s with
    the boolean function [beq_id]. *)

(** **** Exercise: 2 stars (beq_idP)  *)
(** Prove the following: 

[[
  Lemma beq_idP : forall x y, reflect (x = y) (beq_id x y).
]]

*)


(** Now, given [id]s [x1] and [x2], we can use the [destruct (beq_idP
    x1 x2)] to simultaneously perform case analysis on the result of
    [beq_id x1 x2] and generate hypotheses about the equality (in the
    sense of [=]) of [x1] and [x2]. *)

(** **** Exercise: 2 stars (t_update_same)  *)
(** Use [beq_idP] to prove the following theorem, which states that if
    we update a map to assign key [x] the same value as it already has
    in [m], then the result is equal to [m]: 

[[
  Theorem t_update_same : forall X x (m : total_map X),
    t_update m x (m x) = m.
]]

*)



(** **** Exercise: 3 stars, recommended (t_update_permute)  *)
(** Use [beq_idP] to prove one final property of the [update]
    function: If we update a map [m] at two distinct keys, it doesn't
    matter in which order we do the updates. 

[[
  Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
    x2 <> x1 ->
      (t_update (t_update m x2 v2) x1 v1)
    = (t_update (t_update m x1 v1) x2 v2).
]]

*)



(* ################################################################# *)
(** * Expressions With Variables *)

(** Let's turn our attention back to defining Imp.  The next thing we
    need to do is to enrich our arithmetic and boolean expressions
    with variables.  To keep things simple, we'll assume that all
    variables are global and that they only hold numbers. *)

(* ================================================================= *)
(** ** States *)

(** Since we'll want to look variables up to find out their current
    values, we'll reuse the type [id] for the type of variables in
    Imp.

    A _machine state_ (or just _state_) represents the current values
    of _all_ variables at some point in the execution of a program. *)

(** For simplicity, we assume that the state is defined for
    _all_ variables, even though any given program is only going to
    mention a finite number of them.  The state captures all of the
    information stored in memory.  For Imp programs, because each
    variable stores a natural number, we can represent the state as a
    mapping from identifiers to [nat].  For more complex programming
    languages, the state might have more structure. *)

Definition state := total_map nat.

Definition empty_state : state :=
  t_empty 0.

(* ================================================================= *)
(** ** Syntax  *)

(** We can add variables to the arithmetic expressions we had before by
    simply adding one more constructor: *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp                (* <----- NEW *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

(** The definition of [bexp]s is unchanged (except for using the new
    [aexp]s): *)

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(* ================================================================= *)
(** ** Evaluation  *)

(** The arith and boolean evaluators are extended to handle
    variables in the obvious way, taking a state as an extra
    argument: *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.


Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => leb (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Example aexp1 :
  aeval (t_update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2)))
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
  beval (t_update empty_state X 5)
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = true.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Commands *)

(** Now we are ready define the syntax and behavior of Imp
    _commands_ (sometimes called _statements_). *)

(* ================================================================= *)
(** ** Syntax *)

(** Informally, commands [c] are described by the following BNF
    grammar.  (We choose this slightly awkward concrete syntax for the
    sake of being able to define Imp syntax using Coq's Notation
    mechanism.  In particular, we use [IFB] to avoid conflicting with
    the [if] notation from the standard library.)

     c ::= SKIP | x ::= a | c ;; c | IFB b THEN c ELSE c FI 
         | WHILE b DO c END
*)
(**
    For example, here's factorial in Imp:

     Z ::= X;;
     Y ::= 1;;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END

   When this command terminates, the variable [Y] will contain the
   factorial of the initial value of [X]. *)

(** Here is the formal definition of the abstract syntax of
    commands: *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

(** As usual, we can use a few [Notation] declarations to make things
    more readable.  To avoid conflicts with Coq's built-in notations,
    we keep this light -- in particular, we don't introduce any
    notations for [aexps] and [bexps] to avoid confusion with the
    numeric and boolean operators we've already defined. *)

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(** For example, here is the factorial function again, written as a
    formal definition to Coq: *)

Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.

(* ================================================================= *)
(** ** Examples *)

(** Assignment: *)

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
  X ::= AMinus (AId X) (ANum 1).

(* ----------------------------------------------------------------- *)
(** *** Loops *)

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;;
  Z ::= ANum 5 ;;
  subtract_slowly.

(* ----------------------------------------------------------------- *)
(** *** An infinite loop: *)

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

(* ################################################################# *)
(** * Evaluation *)

(** Next we need to define what it means to evaluate an Imp command.
    The fact that [WHILE] loops don't necessarily terminate makes defining
    an evaluation function tricky... *)

(* ================================================================= *)
(** ** Evaluation as a Function (Failed Attempt) *)

(** Here's an attempt at defining an evaluation function for commands,
    omitting the [WHILE] case. *)

Fixpoint ceval_fun_no_while (st : state) (c : com)
                          : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        t_update st x (aeval st a1)
    | c1 ;; c2 =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st  (* bogus *)
  end.

(** In a traditional functional programming language like OCaml or
    Haskell we could add the [WHILE] case as follows:

  Fixpoint ceval_fun (st : state) (c : com) : state :=
    match c with
      ...
      | WHILE b DO c END =>
          if (beval st b)
            then ceval_fun st (c; WHILE b DO c END)
            else st
    end.

    Coq doesn't accept such a definition ("Error: Cannot guess
    decreasing argument of fix") because the function we want to
    define is not guaranteed to terminate. Indeed, it _doesn't_ always
    terminate: for example, the full version of the [ceval_fun]
    function applied to the [loop] program above would never
    terminate. Since Coq is not just a functional programming
    language, but also a consistent logic, any potentially
    non-terminating function needs to be rejected. Here is
    an (invalid!) Coq program showing what would go wrong if Coq
    allowed non-terminating recursive functions:

         Fixpoint loop_false (n : nat) : False := loop_false n.

    That is, propositions like [False] would become provable
    (e.g., [loop_false 0] would be a proof of [False]), which
    would be a disaster for Coq's logical consistency.

    Thus, because it doesn't terminate on all inputs, the full version
    of [ceval_fun] cannot be written in Coq -- at least not without
    additional tricks. *)

(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** Here's a better way: define [ceval] as a _relation_ rather than a
    _function_ -- i.e., define it in [Prop] instead of [Type], as we
    did for [aevalR] above. *)

(** This is an important change.  Besides freeing us from the awkward
    workarounds that would be needed to define evaluation as a
    function, it gives us a lot more flexibility in the definition.
    For example, if we add nondeterministic features like [any] to the
    language, we want the definition of evaluation to be
    nondeterministic -- i.e., not only will it not be total, it will
    not even be a function! *)
(** We'll use the notation [c / st ⇓ st'] for our [ceval] relation:
    [c / st ⇓ st'] means that executing program [c] in a starting
    state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']". *)

(* ----------------------------------------------------------------- *)
(** *** Operational Semantics *)
(** Here is an informal definition of evaluation, presented as inference 
    rules for the sake of readability:

                           ----------------                            (E_Skip)
                           SKIP / st ⇓ st

                           aeval st a1 = n
                   --------------------------------                     (E_Ass)
                   x := a1 / st ⇓ (t_update st x n)

                           c1 / st ⇓ st'
                          c2 / st' ⇓ st''
                         -------------------                            (E_Seq)
                         c1;;c2 / st ⇓ st''

                          beval st b1 = true
                           c1 / st ⇓ st'
                -------------------------------------                (E_IfTrue)
                IF b1 THEN c1 ELSE c2 FI / st ⇓ st'

                         beval st b1 = false
                           c2 / st ⇓ st'
                -------------------------------------               (E_IfFalse)
                IF b1 THEN c1 ELSE c2 FI / st ⇓ st'

                         beval st b = false
                    ------------------------------                 (E_WhileEnd)
                    WHILE b DO c END / st ⇓ st

                          beval st b = true
                           c / st ⇓ st'
                  WHILE b DO c END / st' ⇓ st''
                  ---------------------------------               (E_WhileLoop)
                    WHILE b DO c END / st ⇓ st''
*)

(** Here is the formal definition.  Make sure you understand
    how it corresponds to the inference rules. *)

Reserved Notation "c1 '/' st '⇓' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,

  (*--------------------------------------*)
      SKIP / st ⇓ st
  | E_Ass  : forall st a1 n x,

      aeval st a1 = n ->
  (*--------------------------------------*)
      (x ::= a1) / st ⇓ (t_update st x n)
  | E_Seq : forall c1 c2 st st' st'',

      c1 / st  ⇓ st' ->
      c2 / st' ⇓ st'' ->
  (*--------------------------------------*)
      (c1 ;; c2) / st ⇓ st''
  | E_IfTrue : forall st st' b c1 c2,

      beval st b = true ->
      c1 / st ⇓ st' ->
  (*--------------------------------------*)
      (IFB b THEN c1 ELSE c2 FI) / st ⇓ st'
  | E_IfFalse : forall st st' b c1 c2,

      beval st b = false ->
      c2 / st ⇓ st' ->
  (*--------------------------------------*)
      (IFB b THEN c1 ELSE c2 FI) / st ⇓ st'
  | E_WhileEnd : forall b st c,

      beval st b = false ->
  (*--------------------------------------*)
      (WHILE b DO c END) / st ⇓ st
  | E_WhileLoop : forall st st' st'' b c,

      beval st b = true ->
      c / st ⇓ st' ->
      (WHILE b DO c END) / st' ⇓ st'' ->
  (*--------------------------------------*)
      (WHILE b DO c END) / st ⇓ st''

  where "c1 '/' st '⇓' st'" := (ceval c1 st st').

(** The cost of defining evaluation as a relation instead of a
    function is that we now need to construct _proofs_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)

Example ceval_example1:
    (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   ⇓ (t_update (t_update empty_state X 2) Z 4).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (t_update empty_state X 2).
  - (* assignment command *)
    apply E_Ass. reflexivity.
  - (* if command *)
    apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity.  Qed.

(** **** Exercise: 2 stars (ceval_example2)  *)

(** Show that the following derivation is inhabited:

[[
Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state ⇓
    (t_update (t_update (t_update empty_state X 0) Y 1) Z 2).
]]
*)


(** **** Exercise: 3 stars, advanced (pup_to_n)  *)
(** Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].
   Prove that this program executes as intended for [X] = [2]
   (the latter is trickier than you might expect). 

[[
Definition pup_to_n : com  := _your_definition_ .

Theorem pup_to_2_ceval :
  pup_to_n / (t_update empty_state X 2) ⇓
    t_update (t_update (t_update (t_update (t_update (t_update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
*)


(* ================================================================= *)
(** ** Determinism of Evaluation *)

(** Changing from a computational to a relational definition of
    evaluation is a good move because it allows us to escape from the
    artificial requirement that evaluation should be a total function.
    But it also raises a question: Is the second definition of
    evaluation really a partial function?  Or is it possible that,
    beginning from the same state [st], we could evaluate some command
    [c] in different ways to reach two different output states [st']
    and [st'']?

    In fact, this cannot happen: [ceval] _is_ a partial function: *)

Theorem ceval_deterministic: forall c st st1 st2,
     c / st ⇓ st1  ->
     c / st ⇓ st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1;
           intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b1 evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b1 evaluates to false (contradiction) *)
      rewrite H in H5. inversion H5.
  - (* E_IfFalse, b1 evaluates to true (contradiction) *)
    rewrite H in H5. inversion H5.
  - (* E_IfFalse, b1 evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileEnd, b1 evaluates to false *)
    reflexivity.
  - (* E_WhileEnd, b1 evaluates to true (contradiction) *)
    rewrite H in H2. inversion H2.
  - (* E_WhileLoop, b1 evaluates to false (contradiction) *)
    rewrite H in H4. inversion H4.
  - (* E_WhileLoop, b1 evaluates to true *)
      assert (st' = st'0) as EQ1.
      { (* Proof of assertion *) apply IHE1_1; assumption. }
      subst st'0.
      apply IHE1_2. assumption.  Qed.


(* ################################################################# *)
(** * Reasoning About Imp Programs *)

(** We'll get much deeper into systematic techniques for reasoning
    about Imp programs in the following lectures, but we can do quite
    a bit just working with the bare definitions. *)

(** This section explores some examples. *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st ⇓ st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.

  (** Inverting [Heval] essentially forces Coq to expand one step of
      the [ceval] computation -- in this case revealing that [st']
      must be [st] extended with the new value of [X], since [plus2]
      is an assignment *)

  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.  Qed.

(** **** Exercise: 2 stars, recommended (XtimesYinZ_spec)  *)
(** State and prove a specification of [XtimesYinZ]. *)


(** **** Exercise: 3 stars, recommended (loop_never_stops)  *)

(** By induction on the assumed derivation showing that [loopdef]
    terminates, prove that the program [loop] never terminates.  Most
    of the cases are immediately contradictory (and so can be solved
    in one step with [inversion]). 

[[
  Theorem loop_never_stops : forall st st',
    ~(loop / st ⇓ st').
]] 
*)

Theorem loop_never_stops : forall st st',
  ~(loop / st ⇓ st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef
           eqn:Heqloopdef.
  (* FILL IN HERE *) 

(** **** Exercise: 3 stars (no_whilesR)  *)
(** Consider the definition of the [no_whiles] boolean predicate below: *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP =>
      true
  | _ ::= _ =>
      true
  | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  =>
      false
  end.

(** This predicate yields [true] just on programs that have no while
    loops.  Using [Inductive], write a property [no_whilesR] such that
    [no_whilesR c] is provable exactly when [c] is a program with no
    while loops.  Then prove its equivalence with [no_whiles]. 

[[
Inductive no_whilesR: com -> Prop := _to be defined_.

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
]]

*)


(** **** Exercise: 4 stars (no_whiles_terminating)  *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)
(** Use either [no_whiles] or [no_whilesR], as you prefer. *)


(** **** Exercise: 3 stars, optional (short_circuit)  *)
(** Most modern programming languages use a "short-circuit" evaluation
    rule for boolean [and]: to evaluate [BAnd b1 b2], first evaluate
    [b1].  If it evaluates to [false], then the entire [BAnd]
    expression evaluates to [false] immediately, without evaluating
    [b2].  Otherwise, [b2] is evaluated to determine the result of the
    [BAnd] expression.

    Write an alternate version of [beval] that performs short-circuit
    evaluation of [BAnd] in this manner, and prove that it is
    equivalent to [beval]. *)


(** **** Exercise: 4 stars, optional (add_for_loop)  *)
(** Add C-style [for] loops to the language of commands, update the
    [ceval] definition to define the semantics of [for] loops, and add
    cases for [for] loops as needed so that all the proofs in this file
    are accepted by Coq.

    A [for] loop should be parameterized by (a) a statement executed
    initially, (b) a test that is run on each iteration of the loop to
    determine whether the loop should continue, (c) a statement
    executed at the end of each loop iteration, and (d) a statement
    that makes up the body of the loop.  (You don't need to worry
    about making up a concrete Notation for [for] loops, but feel free
    to play with this too if you like.) *)


(* ################################################################# *)
(** * Conclusion *)

(** ** Lessons learned *)

(** 
- "Denotational semantics" in Maths = "evaluation" in Coq
- "Operational semantics" in Maths = "inductive relation" in Coq
- Meta-theory = "forall e: exp, P e"
 *)

(** ** Take away *)

(**
- you can: give a denotational semantics for a pure language
- you can: give an operational semantics for an effectful language
- you can: prove simple meta-theoretic properties of a small language
 *)