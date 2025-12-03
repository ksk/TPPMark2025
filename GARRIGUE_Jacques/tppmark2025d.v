From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Section lamps.
Variables d' n' : nat.
Local Definition d := d'.+1.  (* number of dimensions (originaly, 3) *)
Local Definition n := n'.+1.  (* size of the hypercube *)

(* A state is a finite function from coordinates to light status *)
Definition state := {ffun d.-tuple 'I_n -> bool}.

Definition mask k c p : k.-tuple 'I_n :=
  [tuple if tnth c i then tnth p i else 0 | i < k].

Lemma mask_id k p : mask [tuple true | _ < k] p = p.
Proof. by apply: eq_from_tnth => i; rewrite !tnth_mktuple. Qed.

(* Sum of the states of corners of the hypercube between the origin and p *)
Definition parity (p : d.-tuple 'I_n) (s : state) := \sum_c s (mask c p).

(* For all coordinates, the corresponding hypercube should satisfy parity *)
Definition cond (s : state) := forall p, parity p s = 0.

Definition face := 'I_d.

Section coord.
Variable (A : Type) (f : face).

(* Insert a coordinate at index f *)
Definition coord (p : A * d'.-tuple A) :=
  [tuple if unlift f i is Some i' then tnth p.2 i' else p.1 | i < d].

(* Project on face f, i.e. remove the coordinate at index f *)
Definition proj (p : d.-tuple A) : d'.-tuple A :=
  [tuple tnth p (lift f i) | i < d'].

Definition projx (p : d.-tuple A) := (tnth p f, proj p).

Lemma projxK : cancel projx coord.
Proof.
move=> p; apply: eq_from_tnth => x; rewrite !tnth_mktuple.
by case: unliftP => [j|] -> //=; rewrite tnth_mktuple.
Qed.

Lemma coordK : cancel coord projx.
Proof.
case=> x p; rewrite /projx /proj !tnth_mktuple unlift_none; congr pair.
by apply: eq_from_tnth => i; rewrite !tnth_mktuple liftK.
Qed.

Lemma coordxK x p : proj (coord (x,p)) = p.
Proof. by have /(f_equal snd) := coordK (x,p). Qed.
End coord.

Definition switch f p0 (s : state) :=
  [ffun p => if proj f p == p0 then ~~ s p else s p].

Definition action : Type := (face * d'.-tuple 'I_n).

Definition switch_seq (l : seq action) (s : state) :=
  foldl (fun s '(f,p) => switch f p s) s l.

Definition empty : state := 0.

Lemma parity_empty : cond empty.
Proof. by move=> p; rewrite /parity big1 // => i _; rewrite !ffunE. Qed.

Definition solvable (s : state) := exists l, switch_seq l s = empty.

Lemma switchK f p : involutive (switch f p).
Proof.
move=> s; apply/ffunP => q; rewrite !ffunE.
by case: (_ == _) => //; rewrite negbK.
Qed.

Lemma switch_seqK l : cancel (switch_seq l) (switch_seq (rev l)).
Proof.
elim: l => // -[f p] l IH s /=.
by rewrite rev_cons [LHS]foldl_rcons -/(switch_seq _ _) IH switchK.
Qed.

Lemma solvableP s : solvable s <-> exists l, switch_seq l empty = s.
Proof. by split => -[l Hl]; exists (rev l); rewrite -Hl switch_seqK. Qed.

(* The corresponding hypercube is degenerate, making parity always true *)
Lemma parity0 (p : d.-tuple 'I_n) s : 0 \in p -> parity p s = 0.
Proof.
case/tnthP => i H.
rewrite /parity (reindex (@coord bool i)) /=;
  last by exists (projx i) => x; rewrite (projxK,coordK).
pose prt j k := s (mask (coord i (j,k)) p).
rewrite (eq_bigr (fun j => prt j.1 j.2)); last by case.
rewrite -pair_bigA_idem //= big_bool /=.
suff: \sum_j prt true j = \sum_j prt false j by move->; rewrite [LHS]addbb.
apply: eq_bigr => /= c _; congr (s _).
by apply: eq_mktuple => k; rewrite !tnth_mktuple; case: unliftP => [l|] ->.
Qed.

(* p is a projection of p0, i.e. it may set some coordinates to 0 *)
Definition is_proj l (p p0 : l.-tuple 'I_n) :=
  [forall i, (tnth p i == 0) || (tnth p i == tnth p0 i)].

(* If p is not a proj. of p0 in f, switching p does not change its parity *)
Lemma parity_disjoint f p p0 s :
  parity p0 s = 0 -> ~~ is_proj p (proj f p0) -> parity p0 (switch f p s) = 0.
Proof.
move=> <- /forallPn[/= x].
rewrite negb_or !tnth_mktuple => /andP[Hx0 Hxp].
apply: eq_bigr => /= c _; rewrite !ffunE ifF // eqEtuple.
apply/negP => /forallP /(_ x); rewrite !tnth_mktuple eq_sym.
by case: ifP => _ ; rewrite (negbTE Hxp, negbTE Hx0). 
Qed.

Lemma parity_face f p (s : state) :
  parity p s = \sum_c \sum_i s (mask (coord f (i,c)) p).
Proof.
rewrite /parity (reindex (@coord bool f)) /=;
  last by exists (projx f) => x; rewrite (projxK,coordK).
pose mc i c := mask (coord f (i,c)) p.
rewrite (eq_bigr (fun j => s (mc j.1 j.2))); last by case.
by rewrite -(pair_bigA_idem _ (fun i c => s (mc i c))) ?addr0 //= exchange_big.
Qed.

(* Switching a row preserves the invariant *)
Lemma switch_inv f p s : cond s -> cond (switch f p s).
Proof.
move: p => /= p Hcond p0. (* Considering the hypercube with corner p0 *)
case/boolP: (0 \in p0) => Hp0; first exact: parity0.
case/boolP: (is_proj p (proj f p0)); last exact: parity_disjoint.
move/forallP => /= Hp.
pose pb := [tuple tnth p i != 0 | i < d'].
rewrite -(Hcond p0) !(parity_face f) !(bigD1 pb (P:=predT)) //=.
congr (_ + _).
  (* Exactly two corners are changed by [switch f p] *)
  rewrite !big_bool /= !ffunE.
  have prmc b : proj f (mask (coord f (b,pb)) p0) == p.
    apply/eqP/eq_from_tnth => i; rewrite !(tnth_mktuple,liftK).
    case/boolP: (tnth p i == 0) (Hp i) => [/eqP | _] //=.
    by rewrite !tnth_mktuple => /eqP.
  by rewrite !prmc [LHS]addNb addbN negbK.
(* All other corners are untouched *)
apply: eq_bigr => c Hc; apply: eq_bigr => i _; rewrite !ffunE ifF //.
apply: contraNF Hc => /eqP eqp.
apply/eqP/eq_from_tnth => j; rewrite /pb -eqp !tnth_mktuple liftK /=.
case: ifP => // _; apply/esym/eqP => Hp0'.
by rewrite -Hp0' mem_tnth in Hp0.
Qed.

Lemma switch_seq_inv l s : cond s -> cond (switch_seq l s).
Proof.
elim/last_ind: l => // l [[f i] j] IH /IH /=.
rewrite /switch_seq foldl_rcons; exact: switch_inv.
Qed.

(* Hyperplane at coordinate 0 from face f *)
Definition hyperface f (s : state) := [ffun p => s (coord f (0, p))].

(* If a face is zeroed, then switching a non-0 coordinate does not change it *)
Lemma switch_hyperface f f' s (p : d'.-tuple 'I_n) :
  hyperface f s = 0 -> s (coord f' (0,p)) -> hyperface f (switch f' p s) = 0.
Proof.
move=> hfs sf'; apply/ffunP => /= q; rewrite !ffunE ifF.
  by move/ffunP/(_ q): hfs; rewrite !ffunE.
move: (sf'); case/boolP: (_ == _) => // /eqP <-.
rewrite -(projxK f (coord f' _)) /projx !tnth_mktuple.
case: (@unlift_some _ f' f).
  by apply/eqP => f'f; move/ffunP/(_ p): hfs; rewrite !ffunE -f'f sf'.
move=> x Hf -> /=; rewrite !tnth_mktuple {2}Hf unlift_none /=.
by set p' := proj f _; move/ffunP/(_ p'): hfs; rewrite !ffunE => ->.
Qed.

Let T' := d'.-tuple 'I_n : finType.
Definition nullify_face f s := [seq (f, q) | q <- enum T' & s (coord f (0, q))].

(* Main step: one can zero hyperfaces one at a time *)
Lemma faces_solvable_step (f g : face) (s : state) :
  (forall (f : face), (f < g)%N -> hyperface f s = 0) ->
  (f <= g)%N -> hyperface f (switch_seq (nullify_face g s) s) = 0.
Proof.
move=> Hl fg; apply/ffunP => /= p; rewrite /nullify_face !ffunE.
have : uniq (enum T') by exact: enum_uniq.
have : (p \in enum T') || (s (coord g (0, p)) == 0) by rewrite mem_enum.
elim: (enum T') s Hl => [s Hl /eqP sg |] /=.
  move: fg; rewrite leq_eqVlt => /orP[/eqP|] fg.
    by have -> : f = g by exact/val_inj.
  by move/(_ _ fg)/ffunP/(_ p): Hl; rewrite !ffunE.
move=> q l IH s /= Hl Hpl /andP[] ql Hu.
case: ifP => Hsp /=.
  rewrite (eq_in_filter (a2:=fun r=> switch g q s (coord g (0,r)))); last first.
    move=> /= r Hr; rewrite !ffunE coordxK ifF //.
    by apply: contraNF ql => /eqP <-.
  apply: IH => //.
    by move=> *; apply: switch_hyperface => //; apply: Hl.
  move: Hpl; rewrite inE.
  case/boolP: (p == q) => [/eqP -> | pq] /=; rewrite !ffunE coordxK.
    by rewrite eqxx Hsp orbT.
  by rewrite (negbTE pq).
apply: IH => //.
move: Hpl; rewrite inE.
by case/boolP: (p == q) => [/eqP -> |] //=; rewrite Hsp orbT.
Qed.

(* By easy? induction, all faces can be solved *)
Lemma faces_solvable s : exists l, forall f, hyperface f (switch_seq l s) = 0.
Proof.
pose m := d.
suff: exists l, forall f : face, (f < m)%N -> hyperface f (switch_seq l s) = 0.
  by case=> l H; exists l => f; apply: H.
elim: m => [|m IH]; first by exists nil => f; rewrite ltn0.
have [l {}IH] := IH.
case: (leqP d m) => dm.
  by exists l => f fm; apply/IH/(leq_trans (ltn_ord f)).
set s' := switch_seq l s in IH.
pose f' : 'I_d := Ordinal dm.
exists (l ++ nullify_face f' s') => f; rewrite ltnS /hyperface => fm.
under eq_ffun do rewrite [switch_seq _ _]foldl_cat -!/(switch_seq _ _).
exact: faces_solvable_step.
Qed.

(* If all faces are solved, then internal positions are solved too *)
Lemma others_solved s :  cond s -> (forall f, hyperface f s = 0) -> s = 0.
Proof.
move=> Hcond Hf.
apply/ffunP => /= p; rewrite !ffunE.
move: (Hcond p); rewrite /parity (bigD1 [tuple true | _ < d]) //= mask_id.
move/(f_equal (+%R (s p))).
rewrite addrA [s p + _]addbb add0r addr0 big1 // => c.
rewrite eqEtuple => /forallPn[/= j].
rewrite !tnth_mktuple eqb_id => /negbTE Hj.
move/(_ j)/ffunP/(_ (proj j (mask c p))): Hf.
by rewrite !ffunE (_ : 0 = tnth (mask c p) j) (projxK,tnth_mktuple) // Hj.
Qed.

Theorem solvability s : solvable s <-> cond s.
Proof.
split => [| Hcond].
  case/solvableP => l <-; exact/switch_seq_inv/parity_empty.
have [l Hf] := faces_solvable s.
exists l; apply: others_solved => //; exact: switch_seq_inv.
Qed.
End lamps.
