From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Definition succO (n : nat) (x : 'I_n) : 'I_n.+1 := lift ord0 x.

Section lamps.
Variable n : nat.
Local Definition n' := n.+1.

Definition plane := 'M[bool]_(n',n').
Definition state := n'.-tuple plane.

Definition parity i j (M : 'M[bool]_(n',n')) :=
  M 0 0 + M i 0 + M 0 j + M i j.

Definition cond (s : state) :=
  forall i j k, parity i j (tnth s 0) = parity i j (tnth s k).

Definition face := option bool.
Definition front : face := None.
Definition side : face := Some false.
Definition vert : face := Some true.

Definition switch_pos i j (p : plane) : plane :=
  \matrix_(x,y) if (x,y) == (i,j) then ~~ p x y else p x y.

Definition switch_row i (p : plane) : plane :=
  \matrix_(x,y) if x == i then ~~ p x y else p x y.

Definition switch_col j (p : plane) : plane :=
  \matrix_(x,y) if y == j then ~~ p x y else p x y.

Definition switch (f : face) i j (s : state) : state :=
  match f with
  | None => map_tuple (switch_pos i j) s
  | Some b =>
      let sw := if b then switch_col else switch_row in
      [tuple if x == i then sw j (tnth s x) else tnth s x | x < n']
  end.

Definition action : Type := (face * 'I_n' * 'I_n').

Definition switch_seq (l : seq action) (s : state) :=
  foldl (fun s '(f,i,j) => switch f i j s) s l.

Definition empty : state := [tuple 0 | _ < _].

Definition solvable (s : state) :=
  exists l, switch_seq l s = empty.

Lemma switch_colK i : involutive (switch_col i).
Proof.
move=> p; apply/matrixP => x y; rewrite !mxE.
case/boolP: (y == i) => // /eqP ->; by rewrite negbK.
Qed.

Lemma switch_rowK i : involutive (switch_row i).
Proof.
move=> p; apply/matrixP => x y; rewrite !mxE.
case/boolP: (x == i) => // /eqP ->; by rewrite negbK.
Qed.

Lemma switch_posK i j : involutive (switch_pos i j).
Proof.
move=> p; apply/matrixP => x y; rewrite !mxE.
case/boolP: (_ == _) => // /eqP [] -> ->; by rewrite negbK.
Qed.

Lemma switchK f i j : involutive (switch f i j).
Proof.
move=> s; case: f => [b|] /=.
- apply/eq_from_tnth => x /=.
  rewrite !tnth_mktuple.
  case/boolP: (x == i) => // /eqP ->.
  by case: b; rewrite (switch_colK,switch_rowK).
- apply/eq_from_tnth => x /=.
  by rewrite !tnth_map switch_posK.
Qed.

Lemma switch_inv f i j s : cond s -> cond (switch f i j s).
Proof.
rewrite /cond.
case: f => [b|] /= H x y z; rewrite ?tnth_mktuple.
- case: ifPn => [/eqP|] i0.
    subst i.
    case/boolP: (z == 0) => [/eqP->|iz] //.
    case: b; rewrite -H /parity !mxE;
    by do! (case/boolP: (_ == _) => [/eqP | ?]); subst;
       rewrite ?[_ + ~~ _]addbN ?[~~ _ + _]addNb ?(addNb,addbN,negbK).
  case: ifPn => [/eqP->|iz] //.
  case: b; rewrite (H _ _ i) /parity !mxE;
  by do! (case/boolP: (_ == _) => [/eqP | ?]); subst;
     rewrite ?[_ + ~~ _]addbN ?[~~ _ + _]addNb ?(addNb,addbN,negbK).
- rewrite !tnth_map /parity !mxE.
  do! (case/boolP: (_ == _) => [/eqP[]?? | ?]); subst;
    rewrite ?[_ + ~~ _]addbN ?[~~ _ + _]addNb ?(addNb,addbN,negbK) //;
    try congr negb; exact: H.
Qed.

Lemma switch_seq_inv l s : cond s -> cond (switch_seq l s).
Proof.
elim/last_ind: l => // l [[f i] j] IH /IH /=.
rewrite /switch_seq foldl_rcons; exact: switch_inv.
Qed.

Lemma switch_seqK l : cancel (switch_seq l) (switch_seq (rev l)).
Proof.
elim: l => // -[[f i] j] l IH s /=.
by rewrite rev_cons [LHS]foldl_rcons -/(switch_seq _ _) IH switchK.
Qed.

Lemma solvableP s : solvable s <-> exists l, switch_seq l empty = s.
Proof. by split => -[l Hl]; exists (rev l); rewrite -Hl switch_seqK. Qed.

Definition nullify0 (s : state) : seq action :=
  [seq (None, i, j) | '(i,j) <- enum (('I_n' * 'I_n')%type : finType)
                    & tnth s 0 i j].

Definition nullify_first_col (p : plane) : seq 'I_n' :=
  [seq i <- enum 'I_n' | p i 0].

Definition nullify_cols (p : plane) : seq 'I_n' :=
  [seq j <- enum 'I_n' | p 0 j].

Lemma tnth_switch_front i j k s :
  tnth (switch front i j s) k = switch_pos i j (tnth s k).
Proof. by rewrite /= tnth_map. Qed.

Lemma tnth_switch_seq_front l s i :
  (all (fun '(a,_,_) => a == front) l) ->
  tnth (switch_seq l s) i =
  foldl (fun s '(_,i,j) => switch_pos i j s) (tnth s i) l.
Proof.
elim: l s => //= -[[a j] k] l IH s /andP[/eqP ->] Ha.
by rewrite IH // tnth_switch_front.
Qed.

Lemma switch_pos_seq_notin (l : seq ('I_n' * 'I_n')) (s : plane) i j :
  ((i, j) \notin l) ->
  foldl (fun z '(x,y) => switch_pos x y z) s l i j = s i j.
Proof.
elim: l s => //= -[a b] l IH s.
rewrite inE negb_or => /andP[ijab Hl].
rewrite IH //.
rewrite !mxE; case: ifP => // /eqP [] ??; subst.
by rewrite eqxx in ijab.
Qed.

Lemma foldl_map T1 T2 (h : T1 -> T2) R (f : R -> T2 -> R) z0 s :
  foldl f z0 [seq h i | i <- s] = foldl (fun z x => f z (h x)) z0 s.
Proof. by elim: s z0 => //=. Qed.

Lemma eq_foldl T R (f g : R -> T -> R) z s :
  f =2 g -> foldl f z s = foldl g z s.
Proof. by move=> fg; elim: s z => //= a s IH z; rewrite IH fg. Qed.

Lemma nullify0_ok s : tnth (switch_seq (nullify0 s) s) 0 = 0.
Proof.
apply/matrixP => i j.
rewrite /nullify0 !mxE.
rewrite tnth_switch_seq_front; last first.
  by apply/allP => /= -[[f] a b] /mapP[] /= [c d] _ /= [] ->.  
set T := ('I_n' * 'I_n')%type : finType.
have := enum_uniq T.
have : (i,j) \in enum T by rewrite mem_enum.
elim: (enum T) (tnth s 0) => //= -[x y] l IH p.
rewrite inE => /orP[/eqP [] <- <- | il] /andP[xl ul].
  rewrite foldl_map (eq_foldl (g := fun z '(x,y) => switch_pos x y z)) /=;
    last by move=> z [t1 t2].
  case: ifP => Hij /=.
    rewrite switch_pos_seq_notin.
      by rewrite !mxE eqxx Hij.
    by rewrite mem_filter negb_and Hij.
  by rewrite switch_pos_seq_notin // mem_filter negb_and Hij.
case: ifP => Hij => /=.
  rewrite (eq_in_filter (a2:=fun '(a, b) => switch_pos x y p a b)).
    exact: IH.
  case=> a b H.
  rewrite !mxE.
  case: ifP => // /eqP abxy.
  by rewrite -abxy H in xl.
exact: IH.
Qed.

Lemma switch_row_seq i l p :
  i \notin l ->
  foldr switch_row p [seq x <- l | p x 0] i 0 = p i 0.
Proof.
elim: l => //= a l IH.
rewrite inE negb_or => /andP[ia il].
case: (p a 0) => /=.
  by rewrite mxE (negbTE ia) IH.
exact: IH.
Qed.

Lemma solve_first_col p :
  col 0 (foldr switch_row p (nullify_first_col p)) = 0.
Proof.
rewrite /nullify_first_col.
apply/colP => i.
rewrite !mxE.
have := enum_uniq 'I_n'.
have : i \in enum 'I_n' by rewrite mem_enum.
elim: (enum 'I_n') p => //= -x l IH p.
rewrite inE => /orP[/eqP <- | il] /andP[xl ul].
  case: ifP => pi0 /=.
    by rewrite mxE eqxx switch_row_seq // pi0.
  by rewrite switch_row_seq // pi0.
case: (p x 0) => /=.
  rewrite mxE.
  case: ifPn => [/eqP|] ix.
    by rewrite -ix il in xl.
  exact: IH.
exact: IH.
Qed.

Lemma switch_col_seq p i j l :
  j \notin l ->
  foldr switch_col p [seq j0 <- l | p 0 j0] i j = p i j.
Proof.
elim: l => //= a l IH.
rewrite inE negb_or => /andP[ja jl].
case: (p 0 a) => /=.
  by rewrite mxE (negbTE ja) IH.
exact: IH.
Qed.

Lemma solve_cols p :
  (forall i j, parity i j p = 0) ->
  col 0 p = 0 ->
  foldr switch_col p (nullify_cols p) = 0.
Proof.
rewrite /nullify_cols => Hpar Hcol.
apply/matrixP => i j.
rewrite !mxE.
have := enum_uniq 'I_n'.
have : j \in enum 'I_n' by rewrite mem_enum.
elim: (enum 'I_n') p Hpar Hcol => //= -x l IH p Hpar Hcol.
have pij : p 0 j + p i j = 0.
  have := Hpar i j.
  rewrite /parity.
  move/colP/(_ 0): (Hcol).
  move/colP/(_ i): Hcol.
  rewrite !mxE => -> ->.
  by rewrite !add0r.
rewrite inE => /orP[/eqP <- | il] /andP[xl ul].
  case/boolP: (p 0 j) => p0j /=.
    rewrite !mxE eqxx switch_col_seq //.
    by rewrite p0j [LHS]addTb in pij.
  rewrite switch_col_seq //.
  by rewrite (negbTE p0j) [LHS]addFb in pij.
case: (p 0 x) => /=.
  rewrite !mxE.
  case: ifPn => [/eqP|] jx.
    by rewrite -jx il in xl.
  exact: IH.
exact: IH.
Qed.

Lemma tnth_switch_seq_plane l s i :
  (all (fun '(a,j,_) => (a != front) && (j != i)) l) ->
  tnth (switch_seq l s) i = tnth s i.
Proof.
elim: l s => //= -[[[a|] j] k] l IH s /andP[] /andP[Ha Hj] Hall //=.
by rewrite IH // tnth_mktuple eq_sym (negbTE Hj).
Qed.

Lemma switch_seq_plane f b s :
  switch_seq [seq (Some b, i, j) | i <- enum 'I_n', j <- f (tnth s i)] s =
  map_tuple
    (fun p => foldr (if b then switch_col else switch_row) p (rev (f p))) s.
Proof.
apply: eq_from_tnth => i.
rewrite tnth_map.
have := enum_uniq 'I_n'.
set s' := s.
rewrite {-2}/s'.
have : i \in enum 'I_n' -> tnth s' i = tnth s i by [].
have : i \in enum 'I_n' by rewrite mem_enum.
elim: (enum _) s' => //= a l IH s'.
rewrite inE => /orP[/eqP <- | ia] Hs' /andP[il ul].
  rewrite [switch_seq _ _]foldl_cat.
  rewrite tnth_switch_seq_plane; last first.
    apply/allP => /= -[] [] g x y // /flattenP[]/= ? /mapP[] /= j jl ->.
    case/mapP => /= k _ [] *; subst.
    rewrite andTb.
    case/boolP: (_ == _) => // /eqP ji.
    by rewrite -ji jl in il.
  elim/last_ind: (f (tnth s i)) => //= [|a' l' {}IH].
    by rewrite Hs' // eqxx.
  by rewrite map_rcons foldl_rcons rev_rcons /= tnth_mktuple eqxx IH.
rewrite [switch_seq _ _]foldl_cat IH // => _.
rewrite tnth_switch_seq_plane //.
  by rewrite Hs' // ia orbT.
apply/allP => /= [] [[g x] y] /mapP[] /= j _ [] *; subst.
rewrite /=; apply/eqP => ai.
by rewrite ai ia in il.
Qed.

Theorem solvability s : cond s <-> solvable s.
Proof.
split; last first.
  case/solvableP => l <-.
  have : cond empty.
    move=> i j k.
    by rewrite /parity !tnth_mktuple !mxE.
  exact: switch_seq_inv.
move=> Hs.
have Hnull0 := nullify0_ok s.
set s' := switch_seq _ _ in Hnull0.
have Hfst i := solve_first_col (tnth s' i).
pose l' := [seq (side, i, j)
          | i <- enum 'I_n',
            j <- rev (nullify_first_col (tnth s' i))].
pose s'' := switch_seq l' s'.
pose l'' := [seq (vert, i, j)
            | i <- enum 'I_n',
              j <- rev (nullify_cols (tnth s'' i))].
exists (nullify0 s ++ l' ++ l'').
rewrite [switch_seq _ _]foldl_cat foldl_cat.
rewrite -!/(switch_seq _ _) -/s'.
rewrite /l'' /vert.
rewrite (switch_seq_plane (fun p => rev (nullify_cols p))).
have Hs''0 : tnth s'' 0 = 0.
  rewrite /s'' /l'.
  rewrite (switch_seq_plane (fun p => rev (nullify_first_col p))).
  rewrite tnth_map revK.
  rewrite (_ : nullify_first_col _ = nil) //.
  rewrite /nullify_first_col (eq_filter (a2:=pred0)) ?filter_pred0 //.
  by move=> j; rewrite Hnull0 mxE.
have Hs'' i j k : parity i j (tnth s'' k) = 0.
   have <- : cond s''.
      exact/switch_seq_inv/switch_seq_inv.
   by rewrite /parity Hs''0 !mxE !addr0.
apply: eq_from_tnth => i.
rewrite !tnth_map !revK.
apply: solve_cols => //.
rewrite /s'' /l'.
rewrite (switch_seq_plane (fun p => rev (nullify_first_col p))).
by rewrite tnth_map revK solve_first_col.
Qed.
End lamps.
