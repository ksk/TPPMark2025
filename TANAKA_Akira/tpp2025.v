From mathcomp Require Import all_ssreflect.
From HB Require Import structures.
Require Import Ring.

Import EqNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Exclusive-OR for sets *)
Definition setE [T : finType] (s1 s2 : {set T}) : {set T} := (s1 :\: s2) :|: (s2 :\: s1).
Notation "a :+: b" := (setE a b) (at level 50, left associativity) : set_scope.
Arguments setE : simpl never.

Section Util.

Lemma in_setE [T : finType] (x : T) (s1 s2 : {set T}) :
  x \in s1 :+: s2 = (x \in s1) (+) (x \in s2).
Proof.
  rewrite !in_set.
  by case: (x \in s1); case: (x \in s2).
Qed.

Lemma setIEl [T : finType] (s1 s2 : {set T}) :
  (s1 :+: s2) :&: s2 = s2 :\: s1.
Proof.
  apply/setP => x.
  rewrite /setE !in_set.
  by case: (x \in s1); case: (x \in s2).
Qed.

Lemma setDEl [T : finType] (s1 s2 : {set T}) :
  (s1 :+: s2) :\: s2 = s1 :\: s2.
Proof.
  apply/setP => x.
  rewrite /setE !in_set.
  by case: (x \in s1); case: (x \in s2).
Qed.

Lemma disjoint_cardsU [T : finType] (A B : {set T}) :
  [disjoint A & B] -> #|A :|: B| = #|A| + #|B|.
Proof.
  rewrite cardsU.
  move/disjoint_setI0 => ->.
  by rewrite cards0 subn0.
Qed.

Lemma disjointIl [T : finType] (s0 s1 s2 : {set T}) :
  [disjoint s1 & s2] -> [disjoint s0 :&: s1 & s0 :&: s2].
Proof.
  rewrite -2!setI_eq0 => /eqP.
  rewrite (@setI T).[AC (2*2) ((2*4)*(1*3))].
  by move=> -> /[! set0I].
Qed.

Lemma set1I [T : finType] (x : T) (A : {set T}) :
  [set x] :&: A = if x \in A then [set x] else set0.
Proof.
  apply/setP => y.
  rewrite 3!fun_if.
  rewrite in_setI in_set1 in_set0.
  case: (boolP (y == x)) => /=.
    move/eqP => ->.
    by case: (x \in A).
  by rewrite if_same.
Qed.

Lemma cards1I [T : finType] (x : T) (A : {set T}) : #|[set x] :&: A| = (x \in A).
Proof.
  rewrite set1I.
  case: (x \in A).
    by rewrite cards1.
  by rewrite cards0.
Qed.

Lemma notin_imset [T1 T2 : finType] [f g : T1 -> T2]
    (H : forall x1 x2, f x1 != g x2) (x : T1) (A : {set T1}) :
  (f x) \in [set g y | y in A] = false.
Proof.
  apply/imsetP.
  case=> x1 _.
  move/eqP.
  by rewrite (negbTE (H x x1)).
Qed.

Lemma injective2_pair (T1 T2 : Type) : injective2 (@pair T1 T2).
Proof.
  move=> x1 x2 y1 y2 [] -> ->.
  by exact (erefl, erefl).
Qed.

Lemma eq_in_pair1 (m : nat) (a b a' : 'I_m) :
  ((a, b) \in [set (a', x) | x : 'I_m]) = (a == a').
Proof.
  apply/imsetP => /=.
  case: ifPn.
    move=> /eqP <-.
    by exists b.
  move=> /eqP a_ne_a'.
  case=> b' _ [] Ha Hb.
  by apply a_ne_a'.
Qed.

Lemma eq_in_pair2 (m : nat) (a b b' : 'I_m) :
  ((a, b) \in [set (x, b') | x : 'I_m]) = (b == b').
Proof.
  apply/imsetP => /=.
  case: ifPn.
    move=> /eqP <-.
    by exists a.
  move=> /eqP b_ne_b'.
  case=> a' _ [] Ha Hb.
  by apply b_ne_b'.
Qed.

Lemma xorb_addb (a b : bool) : xorb a b = a (+) b.
Proof.
  by case: a.
Qed.

End Util.

Section AnyShape.

Variable switch : finType.
Variable lump : finType.

Variable switches_of_lump : lump -> {set switch}.

(* addb is xor for bool *)
Definition status (sws : seq switch) (l : lump) : bool :=
  \big[addb/false]_(sw <- sws) (sw \in switches_of_lump l).

Definition status_set (swset : {set switch}) (l : lump) : bool :=
  odd #|swset :&: switches_of_lump l|.

Definition odd_switches (sws : seq switch) : {set switch} :=
  [set:: [seq sw <- sws | odd (count_mem sw sws)]].

Lemma uniq_status_set (sws : seq switch) (l : lump) :
  uniq sws -> status sws l = status_set [set:: sws] l.
Proof.
  rewrite /status /status_set.
  elim: sws.
    move=> _.
    by rewrite big_nil set0I cards0.
  move=> sw sws IH /=.
  move=> /andP [sw_notin_sws uniq_sws].
  have {uniq_sws}IH := IH uniq_sws.
  rewrite big_cons {}IH.
  rewrite set_cons.
  rewrite setIUl.
  rewrite disjoint_cardsU; last first.
    rewrite -setI_eq0.
    rewrite setIACA.
    rewrite set1I.
    rewrite in_set.
    rewrite (negbTE sw_notin_sws).
    by rewrite set0I.
  by rewrite cards1I oddD oddb.
Qed.

Lemma status_set_status (swset : {set switch}) (l : lump) :
  status_set swset l = status (enum swset) l.
Proof.
  rewrite uniq_status_set; last by apply enum_uniq.
  by rewrite set_enum.
Qed.

Lemma status_cat (sws1 sws2 : seq switch) (l : lump) :
  status (sws1 ++ sws2) l = status sws1 l (+) status sws2 l.
Proof.
  rewrite /status.
  by rewrite big_cat /=.
Qed.

Lemma status_nil (l : lump) :
  status [::] l = false.
Proof.
  rewrite /status.
  by rewrite big_nil.
Qed.

Lemma status_cons (sw : switch) (sws : seq switch) (l : lump) :
  status (sw :: sws) l = (sw \in switches_of_lump l) (+) status sws l.
Proof.
  rewrite /status.
  by rewrite big_cons.
Qed.

Lemma status_seq1 (sw : switch) (l : lump) :
  status [:: sw] l = (sw \in switches_of_lump l).
Proof.
  by rewrite status_cons status_nil addbF.
Qed.

Lemma status_setE (s1 s2 : {set switch}) (l : lump) :
  status (enum (s1 :+: s2)) l = status (enum s1) l (+) status (enum s2) l.
Proof.
  rewrite /status.
  rewrite 3!big_enum /=.
  rewrite (big_setID (A:=s1) s2) /=.
  rewrite (big_setID (A:=s2) s1) /=.
  rewrite addbACA setIC addbb addFb.
  rewrite (big_setID (A:=(s1 :+: s2)) s2) /=.
  by rewrite setIEl setDEl addbC.
Qed.

Lemma odd_switches_cat (sws1 sws2 : seq switch) :
  odd_switches (sws1 ++ sws2) = odd_switches sws1 :+: odd_switches sws2.
Proof.
  rewrite /odd_switches.
  apply/setP => sw.
  rewrite in_set.
  rewrite /setE in_set 2!in_setD !in_set.
  rewrite mem_filter count_cat oddD mem_cat.
  rewrite !mem_filter.
  have HH sws : odd (count_mem sw sws) = true -> sw \in sws.
    move=> H1.
    apply/count_memPn => H.
    by rewrite H in H1.
  case H1: (odd (count_mem sw sws1)); case H2: (odd (count_mem sw sws2)) => /=.
        by rewrite (HH sws1 H1) (HH sws2 H2).
      by rewrite (HH sws1 H1).
    by rewrite (HH sws2 H2) orbT.
  by [].
Qed.

Lemma odd_switches_nil :
  odd_switches nil = set0.
Proof.
  rewrite /odd_switches.
  by rewrite set_nil.
Qed.

Lemma odd_switches_cons (sw : switch) (sws : seq switch) :
  odd_switches (sw :: sws) = [set sw] :+: odd_switches sws.
Proof.
  rewrite -cat1s odd_switches_cat.
  congr (_ :+: odd_switches sws).
  rewrite /odd_switches.
  by rewrite /= eq_refl addn0 /= set_seq1.
Qed.

Lemma odd_switches_ok (sws : seq switch) (l : lump) :
  status (enum (odd_switches sws)) l = status sws l.
Proof.
  elim: sws.
    rewrite status_nil.
    by rewrite odd_switches_nil enum_set0 status_nil.
  move=> sw sws IH.
  rewrite odd_switches_cons status_cons.
  rewrite status_setE {}IH.
  congr (_ (+) status sws l).
  rewrite enum_set1.
  by rewrite status_seq1.
Qed.

Lemma status_status_set (sws : seq switch) (l : lump) :
  status sws l = status_set (odd_switches sws) l.
Proof.
  have:= @uniq_status_set (enum (odd_switches sws)) l.
  rewrite enum_uniq => /(_ isT).
  rewrite odd_switches_ok => ->.
  by rewrite set_enum.
Qed.

Lemma seqswitch_to_setswitch (lumps : {set lump}) :
  (exists (sws : seq switch), forall (l : lump), status sws l = (l \in lumps)) ->
  (exists (swset : {set switch}), forall (l : lump), status_set swset l = (l \in lumps)).
Proof.
  case=> /= sws H.
  exists (odd_switches sws).
  move=> l.
  rewrite -status_status_set.
  by apply H.
Qed.

Lemma setswitch_to_seqswitch (lumps : {set lump}) :
  (exists (swset : {set switch}), forall (l : lump), status_set swset l = (l \in lumps)) ->
  (exists (sws : seq switch), forall (l : lump), status sws l = (l \in lumps)).
Proof.
  case=> /= swset H.
  exists (enum swset).
  move=> l.
  rewrite -status_set_status.
  by apply H.
Qed.

End AnyShape.

Module CubeT.
Section CubeT.

Variable n : nat.

Definition xType := 'I_n.
Definition yType := 'I_n.
Definition zType := 'I_n.

Definition lump : Type := xType * yType * zType.

Arguments xType : simpl never.
Arguments yType : simpl never.
Arguments zType : simpl never.
Arguments lump : simpl never.

Inductive switch :=
| inxy : (xType * yType) -> switch
| inyz : (yType * zType) -> switch
| inzx : (zType * xType) -> switch.

Lemma sum_of_switchK : cancel
  (fun (sw : switch) =>
    match sw with
    | inxy xy => inl (inl xy)
    | inyz yz => inl (inr yz)
    | inzx zx => inr zx
    end)
  (fun (v : (xType * yType) + (yType * zType) + (zType * xType)) =>
    match v with
    | inl (inl xy) => inxy xy
    | inl (inr yz) => inyz yz
    | inr zx       => inzx zx
    end).
Proof. by case; case. Qed.

HB.instance Definition _ := Finite.copy switch (can_type sum_of_switchK).

End CubeT.
End CubeT.

Module Cube1.
Import CubeT.
Section Cube1.

Variable n : nat.

Notation xType := (xType n.+1).
Notation yType := (yType n.+1).
Notation zType := (zType n.+1).
Notation lump := (lump n.+1).
Notation switch := (switch n.+1).
Notation inxy := (@inxy n.+1).
Notation inyz := (@inyz n.+1).
Notation inzx := (@inzx n.+1).

Variable switches_of_lump : lump -> {set switch}.
Hypothesis connection :
  forall (x : xType) (y : yType) (z : zType),
    switches_of_lump (x, y, z) = [set (inxy (x, y)); (inyz (y, z)); (inzx (z, x))].

Notation status := (status switches_of_lump).
Notation status_set := (status_set switches_of_lump).

Lemma injective_inxy : injective inxy.
Proof. by move=> [] /= a b [] c d /= [] -> ->. Qed.

Lemma injective_inyz : injective inyz.
Proof. by move=> [] /= a b [] c d /= [] -> ->. Qed.

Lemma injective_inzx : injective inzx.
Proof. by move=> [] /= a b [] c d /= [] -> ->. Qed.

Lemma inxy_ne_inyz a b : inxy a != inyz b. Proof. by []. Qed.
Lemma inxy_ne_inzx a b : inxy a != inzx b. Proof. by []. Qed.
Lemma inyz_ne_inzx a b : inyz a != inzx b. Proof. by []. Qed.
Lemma inyz_ne_inxy a b : inyz a != inxy b. Proof. by []. Qed.
Lemma inzx_ne_inxy a b : inzx a != inxy b. Proof. by []. Qed.
Lemma inzx_ne_inyz a b : inzx a != inyz b. Proof. by []. Qed.

Ltac simpl_inXX_in_inXX :=
  repeat rewrite [in (inxy _ \in [set inyz _ | _ in _])]imset_comp (notin_imset inxy_ne_inyz);
  repeat rewrite [in (inxy _ \in [set inzx _ | _ in _])]imset_comp (notin_imset inxy_ne_inzx);
  repeat rewrite [in (inyz _ \in [set inxy _ | _ in _])]imset_comp (notin_imset inyz_ne_inxy);
  repeat rewrite [in (inyz _ \in [set inzx _ | _ in _])]imset_comp (notin_imset inyz_ne_inzx);
  repeat rewrite [in (inzx _ \in [set inxy _ | _ in _])]imset_comp (notin_imset inzx_ne_inxy);
  repeat rewrite [in (inzx _ \in [set inyz _ | _ in _])]imset_comp (notin_imset inzx_ne_inyz);
  repeat (rewrite [in (inxy _ \in [set inxy _ | _ in _])](mem_imset _ _ injective_inxy) ||
          rewrite [in (inxy _ \in [set inxy _ | _ in _])]imset_comp (mem_imset _ _ injective_inxy));
  repeat (rewrite [in (inyz _ \in [set inyz _ | _ in _])](mem_imset _ _ injective_inyz) ||
          rewrite [in (inyz _ \in [set inyz _ | _ in _])]imset_comp (mem_imset _ _ injective_inyz));
  repeat (rewrite [in (inzx _ \in [set inzx _ | _ in _])](mem_imset _ _ injective_inzx) ||
          rewrite [in (inzx _ \in [set inzx _ | _ in _])]imset_comp (mem_imset _ _ injective_inzx));
  rewrite ?orbF ?orFb.

Lemma status_set_swset (swset : {set switch}) (x : xType) (y : yType) (z : zType) :
  status_set swset (x, y, z) = ((inxy (x, y)) \in swset) (+)
                               ((inyz (y, z)) \in swset) (+)
                               ((inzx (z, x)) \in swset).
Proof.
  rewrite /status_set connection.
  rewrite setIUr.
  rewrite disjoint_cardsU; last first.
    apply disjointIl.
    rewrite -setI_eq0.
    rewrite setIC set1I.
    by rewrite in_set 2!in_set1.
  rewrite setIUr.
  rewrite disjoint_cardsU; last first.
    apply disjointIl.
    rewrite -setI_eq0.
    rewrite set1I.
    by rewrite in_set1.
  do 3 rewrite setIC cards1I.
  by rewrite !oddD !oddb.
Qed.

Definition xy_switches_for_lumpset (lumps : {set lump}) : {set xType * yType} :=
  [set (x, y) | x in xType, y in yType & (x, y, ord0) \in lumps].

Definition yz_switches_for_lumpset (lumps : {set lump}) : {set yType * zType} :=
  [set (y, z) | y in yType, z in zType &
   ((ord0, y, ord0) \in lumps) (+) ((ord0, y, z) \in lumps)].

Definition zx_switches_for_lumpset (lumps : {set lump}) : {set zType * xType} :=
  [set (z, x) | z in zType, x in xType &
    ((ord0, ord0, ord0) \in lumps) (+) ((ord0, ord0, z) \in lumps) (+)
    ((x, ord0, ord0) \in lumps) (+) ((x, ord0, z) \in lumps)].

Definition all_switches_for_lumpset (lumps : {set lump}) : {set switch} :=
  [set inxy xy | xy in xy_switches_for_lumpset lumps] :|:
  [set inyz yz | yz in yz_switches_for_lumpset lumps] :|:
  [set inzx zx | zx in zx_switches_for_lumpset lumps].

Definition switches_for_lumpset1 (lumps : {set lump}) : option {set switch} :=
  if all (fun '(x, y, z) => ((x, y) \in xy_switches_for_lumpset lumps) (+)
                            ((y, z) \in yz_switches_for_lumpset lumps) (+)
                            ((z, x) \in zx_switches_for_lumpset lumps)
                            == ((x, y, z) \in lumps))
         (enum (setT : {set xType * yType * zType}))
  then
    Some (all_switches_for_lumpset lumps)
  else
    None.

Lemma in_xy_switches_for_lumpset (lumps : {set lump}) (x : xType) (y : yType) :
  ((x, y) \in xy_switches_for_lumpset lumps) = ((x, y, ord0) \in lumps).
Proof.
  rewrite /xy_switches_for_lumpset.
  rewrite mem_imset2; last by apply injective2_pair.
  by rewrite in_set.
Qed.

Lemma in_yz_switches_for_lumpset (lumps : {set lump}) (y : yType) (z : zType) :
  ((y, z) \in yz_switches_for_lumpset lumps) = ((ord0, y, ord0) \in lumps) (+) ((ord0, y, z) \in lumps).
Proof.
  rewrite /yz_switches_for_lumpset.
  rewrite mem_imset2; last apply injective2_pair.
  by rewrite in_set.
Qed.

Lemma in_zx_switches_for_lumpset (lumps : {set lump}) (z : zType) (x : xType) :
  ((z, x) \in zx_switches_for_lumpset lumps)
  = ((ord0, ord0, ord0) \in lumps) (+) ((ord0, ord0, z) \in lumps)
    (+) ((x, ord0, ord0) \in lumps) (+) ((x, ord0, z) \in lumps).
Proof.
  rewrite /zx_switches_for_lumpset.
  rewrite mem_imset2; last apply injective2_pair.
  by rewrite in_set.
Qed.

Lemma switches_for_lumpset1_ok_1 :
  forall (lumps : {set lump}) (swset : {set switch}) (l : lump),
    switches_for_lumpset1 lumps = Some swset ->
    (status_set swset l) = (l \in lumps).
Proof.
  move=> lumps swset l H.
  move: H.
  rewrite /switches_for_lumpset1.
  case: ifPn; last by [].
  move=> H [] <-.
  case: l => -[] x y z.
  rewrite status_set_swset.
  rewrite /all_switches_for_lumpset !in_set;
  simpl_inXX_in_inXX.
  apply/eqP.
  apply (allP H (x, y, z)).
  rewrite mem_enum.
  by apply in_setT.
Qed.

Definition plane_xy_switches (z : zType) : {set switch} :=
  [set inyz (y, z) | y in yType] :|: [set inzx (z, x) | x in xType].

Definition plane_yz_switches (x : xType) : {set switch} :=
  [set inzx (z, x) | z in zType] :|: [set inxy (x, y) | y in yType].

Definition plane_zx_switches (y : yType) : {set switch} :=
  [set inxy (x, y) | x in xType] :|: [set inyz (y, z) | z in zType].

Definition clear_switches_y0_in_yz (swset : {set switch}) : {set switch} :=
  swset :+: \bigcup_(y | (inyz (y, ord0) \in swset)) (plane_zx_switches y).

Definition clear_switches_0x_in_zx (swset : {set switch}) : {set switch} :=
  swset :+: \bigcup_(x | (inzx (ord0, x) \in swset)) (plane_yz_switches x).

Definition clear_switches_z0_in_zx (swset : {set switch}) : {set switch} :=
  swset :+: \bigcup_(z | (inzx (z, ord0) \in swset)) (plane_xy_switches z).

Lemma in_plane_xy_switches (sw : switch) (z0 : zType) :
  sw \in plane_xy_switches z0
  = match sw with
    | CubeT.inxy (x, y) => false
    | CubeT.inyz (y, z) => z == z0
    | CubeT.inzx (z, x) => z == z0
    end.
Proof.
  rewrite /plane_xy_switches.
  rewrite in_setU.
  case: sw => [[x y]|[y z]|[z x]]; simpl_inXX_in_inXX.
      by [].
    by apply eq_in_pair2.
  by apply eq_in_pair1.
Qed.

Lemma in_plane_yz_switches (sw : switch) (x0 : zType) :
  sw \in plane_yz_switches x0
  = match sw with
    | CubeT.inxy (x, y) => x == x0
    | CubeT.inyz (y, z) => false
    | CubeT.inzx (z, x) => x == x0
    end.
Proof.
  rewrite /plane_yz_switches.
  rewrite in_setU.
  case: sw => [[x y]|[y z]|[z x]]; simpl_inXX_in_inXX.
      by apply eq_in_pair1.
    by [].
  by apply eq_in_pair2.
Qed.

Lemma in_plane_zx_switches (sw : switch) (y0 : zType) :
  sw \in plane_zx_switches y0
  = match sw with
    | CubeT.inxy (x, y) => y == y0
    | CubeT.inyz (y, z) => y == y0
    | CubeT.inzx (z, x) => false
    end.
Proof.
  rewrite /plane_zx_switches.
  rewrite in_setU.
  case: sw => [[x y]|[y z]|[z x]]; simpl_inXX_in_inXX.
      by apply eq_in_pair2.
    by apply eq_in_pair1.
  by [].
Qed.

(* solve following or similar
  (inxy (x, y) \in swset)
  (+) (inxy (x, y)
         \in \bigcup_(y0 | inyz (y0, ord0) \in swset)
                plane_zx_switches y0) =
  (inxy (x, y) \in swset)
  (+) (inyz (y, ord0) \in swset)
*)
Ltac solve_in_clear_switches_XX_in_XX_1 u :=
  congr (_ (+) _);
  apply/bigcupP => /=;
  case: ifPn; intros H1; [
    (exists u; first by []);
    by (rewrite in_plane_zx_switches ||
        rewrite in_plane_xy_switches ||
        rewrite in_plane_yz_switches) |
  case; intros w H2;
  (rewrite in_plane_zx_switches ||
   rewrite in_plane_xy_switches ||
   rewrite in_plane_yz_switches);
  move=> /eqP; intros Hw;
  subst w;
  by rewrite H2 in H1 ].

(* solve following or similar
  (inzx (z, x) \in swset)
  (+) (inzx (z, x)
         \in \bigcup_(y | inyz (y, ord0) \in swset)
                plane_zx_switches y) =
  (inzx (z, x) \in swset)
*)
Ltac solve_in_clear_switches_XX_in_XX_2 :=
  rewrite -[RHS]addbF;
  congr (_ (+) _);
  apply/bigcupP => /=;
  case=> u;
  by (rewrite in_plane_zx_switches ||
      rewrite in_plane_xy_switches ||
      rewrite in_plane_yz_switches).

Lemma in_clear_switches_y0_in_yz (sw : switch) (swset : {set switch}) :
  (sw \in (clear_switches_y0_in_yz swset))
  = match sw with
    | CubeT.inxy (x, y) => (sw \in swset) (+) (inyz (y, ord0) \in swset)
    | CubeT.inyz (y, z) => (sw \in swset) (+) (inyz (y, ord0) \in swset)
    | CubeT.inzx (z, x) => (sw \in swset)
    end.
Proof.
  rewrite /clear_switches_y0_in_yz.
  rewrite in_setE.
  case: sw => [[x y]|[y z]|[z x]].
      solve_in_clear_switches_XX_in_XX_1 y.
    solve_in_clear_switches_XX_in_XX_1 y.
  solve_in_clear_switches_XX_in_XX_2.
Qed.

Lemma in_clear_switches_0x_in_zx (sw : switch) (swset : {set switch}) :
  (sw \in (clear_switches_0x_in_zx swset))
  = match sw with
    | CubeT.inxy (x, y) => (sw \in swset) (+) (inzx (ord0, x) \in swset)
    | CubeT.inyz (y, z) => (sw \in swset)
    | CubeT.inzx (z, x) => (sw \in swset) (+) (inzx (ord0, x) \in swset)
    end.
Proof.
  rewrite /clear_switches_0x_in_zx.
  rewrite in_setE.
  case: sw => [[x y]|[y z]|[z x]].
      solve_in_clear_switches_XX_in_XX_1 x.
    solve_in_clear_switches_XX_in_XX_2.
  solve_in_clear_switches_XX_in_XX_1 x.
Qed.

Lemma in_clear_switches_z0_in_zx (sw : switch) (swset : {set switch}) :
  (sw \in (clear_switches_z0_in_zx swset))
  = match sw with
    | CubeT.inxy (x, y) => (sw \in swset)
    | CubeT.inyz (y, z) => (sw \in swset) (+) (inzx (z, ord0) \in swset)
    | CubeT.inzx (z, x) => (sw \in swset) (+) (inzx (z, ord0) \in swset)
    end.
Proof.
  rewrite /clear_switches_z0_in_zx.
  rewrite in_setE.
  case: sw => [[x y]|[y z]|[z x]].
      solve_in_clear_switches_XX_in_XX_2.
    solve_in_clear_switches_XX_in_XX_1 z.
  solve_in_clear_switches_XX_in_XX_1 z.
Qed.

Definition tweak_switches (swset : {set switch}) : {set switch} :=
  let swset2 := clear_switches_y0_in_yz swset in
  let swset3 := clear_switches_0x_in_zx swset2 in
  let swset4 := clear_switches_z0_in_zx swset3 in
  swset4.

Lemma inxy_in_tweak_switches (x : xType) (y : yType) (swset : {set switch}) :
  (inxy (x, y) \in tweak_switches swset)
  = (inxy (x, y) \in swset) (+)
    (inyz (y, ord0) \in swset) (+)
    (inzx (ord0, x) \in swset).
Proof.
  rewrite /tweak_switches.
  rewrite in_clear_switches_z0_in_zx.
  rewrite in_clear_switches_0x_in_zx.
  rewrite in_clear_switches_y0_in_yz.
  rewrite in_clear_switches_y0_in_yz.
  by [].
Qed.

Lemma inyz_in_tweak_switches (y : yType) (z : zType) (swset : {set switch}) :
  (inyz (y, z) \in tweak_switches swset)
  = (inyz (y, z) \in swset) (+)
    (inyz (y, ord0) \in swset) (+)
    (inzx (z, ord0) \in swset) (+)
    (inzx (ord0, ord0) \in swset).
Proof.
  rewrite /tweak_switches.
  rewrite in_clear_switches_z0_in_zx.
  rewrite in_clear_switches_0x_in_zx.
  rewrite in_clear_switches_y0_in_yz.
  rewrite in_clear_switches_0x_in_zx.
  rewrite in_clear_switches_y0_in_yz.
  rewrite in_clear_switches_y0_in_yz.
  by rewrite !addbA.
Qed.

Lemma inzx_in_tweak_switches (z : zType) (x : xType) (swset : {set switch}) :
  (inzx (z, x) \in tweak_switches swset)
  = (inzx (z, x) \in swset) (+)
    (inzx (ord0, x) \in swset) (+)
    (inzx (z, ord0) \in swset) (+)
    (inzx (ord0, ord0) \in swset).
Proof.
  rewrite /tweak_switches.
  rewrite in_clear_switches_z0_in_zx.
  rewrite in_clear_switches_0x_in_zx.
  rewrite in_clear_switches_y0_in_yz.
  rewrite in_clear_switches_y0_in_yz.
  rewrite in_clear_switches_0x_in_zx.
  rewrite in_clear_switches_y0_in_yz.
  rewrite in_clear_switches_y0_in_yz.
  by rewrite !addbA.
Qed.

Lemma switches_for_lumpset1_ok_2 :
  forall (lumps : {set lump}) (swset : {set switch}),
    (forall (l : lump), (status_set swset l) = (l \in lumps)) ->
    switches_for_lumpset1 lumps = Some (tweak_switches swset).
Proof.
  move=> lumps swset H0.
  rewrite /switches_for_lumpset1.
  case: ifPn.
    move=> _.
    congr (Some _).
    apply/setP => sw.
    case: sw => /= [[x y]|[y z]|[z x]].
        rewrite /all_switches_for_lumpset ![in LHS]in_set;
        simpl_inXX_in_inXX.
        rewrite in_xy_switches_for_lumpset -H0 status_set_swset.
        by rewrite inxy_in_tweak_switches.
      rewrite /all_switches_for_lumpset ![in LHS]in_set;
      simpl_inXX_in_inXX.
      rewrite in_yz_switches_for_lumpset.
      do 2 rewrite -H0 status_set_swset.
      rewrite inyz_in_tweak_switches.
      (*
      move: (inxy (ord0, y) \in swset)
            (inyz (y, ord0) \in swset)
            (inyz (y, z) \in swset)
            (inzx (ord0, ord0) \in swset)
            (inzx (z, ord0) \in swset)
        => b1 b2 b3 b4 b5.
      by rewrite -!xorb_addb; ring.
      *)
      by rewrite !addbA addb.[ACl 5*2*6*3*1*4] addbK.
    rewrite /all_switches_for_lumpset ![in LHS]in_set;
    simpl_inXX_in_inXX.
    rewrite in_zx_switches_for_lumpset.
    do 4 rewrite -H0 status_set_swset.
    rewrite inzx_in_tweak_switches.
    (* this case-analysis works but bit slow: (more than 1 second on my machine)
    time by case: (inxy (ord0, ord0) \in swset);
         case: (inxy (x, ord0) \in swset);
         case: (inyz (ord0, ord0) \in swset);
         case: (inyz (ord0, z) \in swset);
         case: (inzx (ord0, ord0) \in swset);
         case: (inzx (ord0, x) \in swset);
         case: (inzx (z, ord0) \in swset);
         case: (inzx (z, x) \in swset). *)
    (*
    move: (inxy (ord0, ord0) \in swset)
          (inxy (x, ord0) \in swset)
          (inyz (ord0, ord0) \in swset)
          (inyz (ord0, z) \in swset)
          (inzx (ord0, ord0) \in swset)
          (inzx (ord0, x) \in swset)
          (inzx (z, ord0) \in swset)
          (inzx (z, x) \in swset)
      => b1 b2 b3 b4 b5 b6 b7 b8.
    by rewrite -!xorb_addb; ring. *)
    by rewrite !addbA addb.[ACl 12*9*6*3*1*4*2*8*5*11*7*10] 4!addbK.
  move/negP => Hall.
  exfalso.
  apply/Hall/allP => /= [[[x y] z] _] {Hall}.
  apply/eqP.
  rewrite in_xy_switches_for_lumpset.
  rewrite in_yz_switches_for_lumpset.
  rewrite in_zx_switches_for_lumpset.
  rewrite -!H0 !status_set_swset.
  (* This works but too slow.  More than 70 seconds on my machine.
  time by case: (inxy (ord0, ord0) \in swset);
          case: (inxy (ord0, y) \in swset);
          case: (inxy (x, ord0) \in swset);
          case: (inxy (x, y) \in swset);
          case: (inyz (ord0, ord0) \in swset);
          case: (inyz (ord0, z) \in swset);
          case: (inyz (y, ord0) \in swset);
          case: (inyz (y, z) \in swset);
          case: (inzx (ord0, ord0) \in swset);
          case: (inzx (ord0, x) \in swset);
          case: (inzx (z, ord0) \in swset);
          case: (inzx (z, x) \in swset). *)
  (* This works but tiring and hard to maintain.
  rewrite !addbA.
  rewrite -!(addbAC _ (inyz (y, ord0) \in swset)) addbK.
  rewrite -!(addbAC _ (inzx (ord0, x) \in swset)) addbK.
  rewrite -!(addbAC _ (inxy (ord0, y) \in swset)) addbK.
  rewrite -!(addbAC _ (inxy (x, ord0) \in swset)) addbK.
  rewrite -!(addbAC _ (inzx (ord0, ord0) \in swset)) addbK.
  rewrite -!(addbAC _ (inzx (z, ord0) \in swset)) addbK.
  rewrite -!(addbAC _ (inxy (ord0, ord0) \in swset)) addbK.
  rewrite -!(addbAC _ (inyz (ord0, ord0) \in swset)) addbK.
  rewrite addbK.
  by []. *)
  (* ring still needs many lines because it doesn't work without abstracting complex subexpressions
  move: (inxy (ord0, ord0) \in swset)
        (inxy (ord0, y) \in swset)
        (inxy (x, ord0) \in swset)
        (inxy (x, y) \in swset)
        (inyz (ord0, ord0) \in swset)
        (inyz (ord0, z) \in swset)
        (inyz (y, ord0) \in swset)
        (inyz (y, z) \in swset)
        (inzx (ord0, ord0) \in swset)
        (inzx (ord0, x) \in swset)
        (inzx (z, ord0) \in swset)
        (inzx (z, x) \in swset)
    => b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12.
  by rewrite -!xorb_addb /=; ring. *)
  by rewrite !addbA addb.[ACl 1*8*21*2*5*3*18*4*7*6*12*9*15*10*13*11*17*14*20*16*19] !addbK.
Qed.

Lemma switches_for_lumpset1_ok' :
  forall (lumps : {set lump}),
    switches_for_lumpset1 lumps <->
    (exists (swset : {set switch}), forall (l : lump),
      (status_set swset l) = (l \in lumps)).
Proof.
  move=> lumps.
  split.
    case H: (switches_for_lumpset1 lumps) => [swset|]; last by [].
    move=> _.
    exists swset => l.
    by apply switches_for_lumpset1_ok_1.
  by case=> swset /switches_for_lumpset1_ok_2 ->.
Qed.

Lemma switches_for_lumpset1_ok (lumps : {set lump}) :
  switches_for_lumpset1 lumps <->
  (exists (sws : seq switch), forall (l : lump),
    (status sws l) = (l \in lumps)).
Proof.
  split.
    case H: (switches_for_lumpset1 lumps) => /= [swset|]; last by [].
    move=> _.
    apply: setswitch_to_seqswitch => /=.
    apply: (iffLR (switches_for_lumpset1_ok' _)).
    by rewrite H.
  move/seqswitch_to_setswitch => /=.
  by move/(iffRL (switches_for_lumpset1_ok' _)).
Qed.

End Cube1.
End Cube1.

Module Cube.
Import CubeT.
Section Cube.

Variable switches_of_lump : forall (n : nat), lump n -> {set switch n}.

Variable connection :
  forall (n : nat) (x : xType n) (y : yType n) (z : zType n),
    switches_of_lump (x, y, z) = [set (inxy (x, y)); (inyz (y, z)); (inzx (z, x))].

Definition switches_for_lumpset (n : nat) (lumps : {set lump n}) : option {set switch n} :=
  match n as n' return n = n' -> option {set switch n} with
  | 0 => fun (H : n = 0) => Some set0
  | m.+1 => fun (H : n = m.+1) =>
      rew <- [fun i => option {set switch i}] H in
        (@Cube1.switches_for_lumpset1 m
          (rew [fun i => ({set lump i})%type] H in lumps))
  end erefl.

Lemma switches_for_lumpset_ok (n : nat) (lumps : {set lump n}) :
  switches_for_lumpset lumps <->
  (exists (sws : seq (switch n)), forall (l : lump n),
    (status (@switches_of_lump n) sws l) = (l \in lumps)).
Proof.
  rewrite /switches_for_lumpset.
  case: n lumps => [|n] lumps.
    split=> [_|]; last by [].
    exists [::] => -[] [] [] m H.
    exfalso.
    by rewrite ltn0 in H.
  apply Cube1.switches_for_lumpset1_ok.
  by apply connection.
Qed.

End Cube.
End Cube.
