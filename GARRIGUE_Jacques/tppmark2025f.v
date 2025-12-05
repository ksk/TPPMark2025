From mathcomp Require Import all_ssreflect all_algebra ring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

(* Based on Taniguchi Masaya's solution
   https://github.com/auto-res/tpp2025/blob/main/tpp2025/Tpp2025.lean
 *)

Definition posnat := {n | n > 0}%N.
Definition nat_of_posnat (n : posnat) := (val n).-1.+1.
Coercion nat_of_posnat : posnat >-> nat.

Section cube.
Variable n : posnat.

Definition cube := {ffun 'I_n * 'I_n * 'I_n -> bool}.
Definition face_action := 'I_n -> 'I_n -> bool.

(* Normal form of a solution: just choose which columns to switch *)
Record XYZ := {X: face_action; Y: face_action; Z: face_action}.

Definition solvable (a : cube) :=
  exists s, forall i j k, X s j k + Y s i k + Z s i j = a (i,j,k).

Definition parity (a : cube) :=
  forall i j k,
    a (i,j,k)
      = a (0,j,k)
      + a (i,0,k)
      + a (i,j,0)
      + a (0,0,k)
      + a (0,j,0)
      + a (i,0,0)
      + a (0,0,0).

Definition constructXYZ (a : cube) : XYZ :=
  {| Z := fun i j => a (i,j,0) ;
     Y := fun i k => a (i,0,k) + a (i,0,0) ;
     X := fun j k => a (0,j,k) + a (0,0,k) + a (0,j,0) + a (0,0,0) |}.

Theorem constructive_solution
    (a : cube)
    (hpar : parity a) :
    forall i j k,
      let s := constructXYZ a in
      X s j k + Y s i k + Z s i j = a (i,j,k).
Proof. move=> i j k /=; rewrite (hpar i j k); ring. Qed.

Theorem solvable_implies_parity a :
  solvable a -> parity a.
Proof.
case=> s H i j k; rewrite -!H.
(* Add duplicates, since ring does not use charateristic *)
do 9! (rewrite -[LHS]addbF).
rewrite -{1}(addbb (X s 0 0)) -{1}(addbb (X s j 0)) -{1}(addbb (X s 0 k)).
rewrite -{1}(addbb (Y s 0 0)) -{1}(addbb (Y s i 0)) -{1}(addbb (Y s 0 k)).
rewrite -{1}(addbb (Z s 0 0)) -{1}(addbb (Z s i 0)) -{1}(addbb (Z s 0 j)).
rewrite -![_ (+) _]/(_ + _); ring.
Qed.

Theorem solvable_iff_parity a :
  solvable a <-> parity a.
Proof.
split; first exact: solvable_implies_parity.
move=> H; exists (constructXYZ a); exact: constructive_solution.
Qed.

(* Extend solution to list of actions *)

Inductive face := FX | FY | FZ.

Definition proj f (pos : 'I_n * 'I_n * 'I_n) :=
  let: (i,j,k) := pos in
  match f with
  | FX => (j,k)
  | FY => (i,k)
  | FZ => (i,j)
  end.

Definition action : Type := face * ('I_n * 'I_n).

Definition ray (a : action) : cube := [ffun pos => proj a.1 pos == a.2].

Definition switch (a : action) (c : cube) := c + ray a.

Definition switch_seq (l : seq action) c := foldr switch c l.

Definition solvable' c := exists l, switch_seq l c = 0.

Definition coord2 : finType := ('I_n * 'I_n)%type.

(* List of action corresponding to a normal solution *)
Definition seq_of_XYZ (s : XYZ) :=
  [seq (FX, ij) | ij <- enum coord2 & X s ij.1 ij.2] ++
  [seq (FY, ij) | ij <- enum coord2 & Y s ij.1 ij.2] ++
  [seq (FZ, ij) | ij <- enum coord2 & Z s ij.1 ij.2].

Lemma switch_seqA l c : switch_seq l c = c + \sum_(a <- l) ray a.
Proof.
elim: l => [|a l IH] /=; first by rewrite big_nil addr0.
by rewrite big_cons IH addrA addrAC.
Qed.

Lemma switch_seqK l : involutive (switch_seq l).
Proof.
move=> c; rewrite !switch_seqA.
by apply/ffunP => /= -[[i j k]]; rewrite !ffunE -addrA [X in _ + X]addbb addr0.
Qed.

Lemma parity0 : parity 0.
Proof. move=> *; rewrite !ffunE; ring. Qed.

Lemma parity_add (c1 c2 : cube) : parity c1 -> parity c2 -> parity (c1 + c2).
Proof. move=> pc1 pc2 i j k; rewrite !ffunE pc1 pc2; ring. Qed.

Lemma parity_ray a : parity (ray a).
Proof. by case: a => -[] p i j k; rewrite !ffunE; do! case: (_ == _). Qed.

(* Invariant is kept by sequence of actions *)
Lemma solvable'_implies_parity c : solvable' c -> parity c.
Proof.
case=> l /(f_equal (switch_seq l)).
rewrite switch_seqK switch_seqA add0r => ->.
apply: big_ind => *; [exact: parity0 | exact: parity_add | exact: parity_ray].
Qed.

(* Only one ray from a given face crosses a given point *)
Lemma sum_cond_ray P f i j k :
  \sum_(p : coord2 | P p) ray (f, p) (i, j, k) = P (proj f (i,j,k)).
Proof.
rewrite big_mkcond (bigD1 (proj f (i,j,k))) // big1 /=.
  by rewrite ffunE eqxx addr0 [LHS]orbF.
by case=> ??; rewrite !ffunE /= eq_sym => /negbTE ->; rewrite if_same.
Qed.

Theorem solvableP c : solvable c <-> solvable' c.
Proof.
split.
- case => s H; exists (seq_of_XYZ s).
  apply/ffunP => /= -[[i j k]].
  rewrite /seq_of_XYZ switch_seqA !big_cat /= !ffunE !sum_ffunE.
  rewrite !big_map !big_filter !big_enum_cond !sum_cond_ray /=.
  by rewrite -[RHS](addbb (c (i,j,k))) -[RHS]/(_ + _) -{3}H !addrA.
- by move /solvable'_implies_parity /solvable_iff_parity.
Qed.
End cube.
