(** ** lC_to_lB0_systems by Vladimir Voevodsky,

started Feb. 15, 2015, renamed Fe. 21, 2015 

We refer below to the paper "Subsystems and regular quotients of C-systems"
by V. Voevodsky as "Csubsystems".

 *)

Require Export lBsystems.lBsystems.
Require Export lCsystems.lCsystems.


Unset Automatic Introduction.

(** *** Constructing the lB-system carrier *)

Definition Tilde_from_C ( CC : ltower_precat_and_p ) :=
  total2 ( fun X : CC => dirprod ( ll X > 0 ) ( Ob_tilde_over X ) ) .


Lemma isaset_Tilde_from_C ( CC : lC0system ) : isaset ( Tilde_from_C CC ) .
Proof.
  intros . set ( is1 := C0_has_homsets CC ) . set ( is2 := C0_isaset_Ob CC ) .  
  apply ( isofhleveltotal2 2 ) . 
  apply is2 . 

  intro X . 
  unfold Ob_tilde_over .
  apply ( isofhleveltotal2 2 ) .

  apply isasetaprop .
  apply ( pr2 ( ll X > 0 ) ) . 

  intro . 
  apply ( isofhleveltotal2 2 ) . 

  apply is1  .

  intro Y .
  apply isasetaprop . 
  apply is1 . 

Defined.

  

Definition dd_from_C { CC : ltower_precat_and_p } ( r : Tilde_from_C CC ) : CC :=
  pr1 r .

Definition ll_dd_from_C { CC : ltower_precat_and_p } ( r : Tilde_from_C CC ) :
  ll ( dd_from_C r ) > 0 := pr1 ( pr2 r ) . 


Definition Tilde_from_C_to_Ob_tilde_over { CC : ltower_precat_and_p } ( r : Tilde_from_C CC ) :
  Ob_tilde_over ( dd_from_C r ) := pr2 ( pr2 r ) .
Coercion Tilde_from_C_to_Ob_tilde_over : Tilde_from_C >-> Ob_tilde_over . 




Definition B_carrier_from_C ( CC : lC0system ) : lBsystem_carrier .
Proof .
  intros .  
  refine ( lBsystem_carrier_constr _ _ ) . 
  refine ( hSet_pltower_constr _ _ ) .
  apply ( hSet_ltower_constr CC ( C0_isaset_Ob CC ) ) . 

  apply ( ispointed CC ) . 

  apply ( tpair _ _ ( isaset_Tilde_from_C CC ) ) . 

  apply dd_from_C . 

  intro r . simpl in r .
  apply ( pr1 ( pr2 r ) ) . 

Defined.






(* Definition Tilde_from_C_to_Tilde_B_carrier_from_C { CC : lC0system } ( r : Tilde_from_C CC ) :
  Tilde ( B_carrier_from_C CC ) := r .
Coercion Tilde_from_C_to_Tilde_B_carrier_from_C : Tilde_from_C >-> Tilde . *) 


(** *** Operation T *)

(** **** Constructing operation T *)

Definition T_from_C ( CC : lC0system ) : T_ops_type ( B_carrier_from_C CC ) . 
Proof.
  intros.
  unfold T_ops_type . 
  intros X1 X2 inn .
  set ( f := pX X1 : ( X1 --> ft X1 ) ) .
  set ( n := ll X2 - ( ll ( ft X1 ) ) ) .
  assert ( e : ftn n X2 = ft X1 ) .
  assert ( isov := isabove_to_isover (T_dom_isabove inn )) .
  
  unfold isover in isov . 
  apply ( ! isov ) .

  assert ( gtn : ll X2 >= n ) . apply natminuslehn .
  
  apply ( fn_star f n gtn e ) . 

Defined.


(** **** Proving properties ax1a, ax1b and ax0 of operation T *)

Lemma T_ax1a_from_C { CC : lC0system } : T_ax1a_type ( T_from_C CC ) .
Proof.
  intros.
  unfold T_ax1a_type.
  intros .
  unfold T_from_C . 
  assert ( eq : ll X2 - ll (ft X1)  = S ( ll ( ft X2 ) - ll ( ft X1 ) ) ) .
  rewrite ( ll_ft X2 ) . 
  rewrite natminuscomm .
  change  ( ll X2 - ll (ft X1) = 1 + ( ll X2 - ll ( ft X1 ) - 1 ) ) .  
  rewrite <- natassocpmeq . 
  simpl . rewrite natminuseqn . 
  apply idpath . 

  apply gth0_to_geh1 . 
  apply minusgth0 . 
  apply ( T_dom_gth inn ) .

  rewrite ( fn_star_to_fsm_star _ _ _ eq ) .
  rewrite fsn_strict . 
  rewrite ( @ft_f_star CC ).
  unfold fn_star . 
  apply ( maponpaths pr1 ) .  apply qn_equals_qn . 
  apply C0_isaset_Ob .

  apply idpath . 
  
Defined.


 
Lemma T_ax1b_from_C ( CC : lC0system ) : T_ax1b_type ( T_from_C CC ) .
Proof.
  intros.
  unfold T_ax1b_type . 
  intros .
  refine ( isabove_constr _ _ ) .
  unfold T_from_C . 
  rewrite (@ll_fn_star CC) . 
  rewrite ll_ft .
  rewrite ( natpluscomm ( ll X1 ) _ ) . 
  change  ( ll X2 - (ll X1 - 1) + ll X1 > 0 + ( ll X1 ) ) . 
  apply natgthandplusr . 
  apply minusgth0 . 
  unfold T_dom in inn . 
  rewrite <- ll_ft .
  apply ( isabove_gth ( T_dom_isabove inn ) ) . 

  unfold T_from_C . apply isover_fn_star . 

Defined.


  

Lemma T_ax0_from_C ( CC : lC0system ) : T_ax0_type ( T_from_C CC ) . 
Proof.
  intros.
  unfold T_ax0_type . 
  intros X1 X2 inn .
  unfold T_from_C . 
  rewrite ( @ll_fn_star CC ) . 
  rewrite ll_ft . 
  rewrite <- natassocmpeq . rewrite <- natplusassoc .  rewrite ( natpluscomm ( ll X1 ) _ ) .
  rewrite minusplusnmm . 
  apply natpluscomm . 

  apply ( T_dom_geh inn ) . 

  apply ( T_dom_geh inn ) . 

  apply ( gth0_to_geh1 ( T_dom_gt0 inn ) ) .

Defined.


(** **** Morphism qT *)

Definition qT { CC : lC0system } { X1 X2 : B_carrier_from_C CC } ( inn : T_dom X1 X2 ) :
  mor_to X2 :=
  qn (pX X1) (ll X2 - ll (ft X1)) (natminuslehn (ll X2) (ll (ft X1)))
     (! ( isabove_to_isover ( T_dom_isabove inn) ) ).

Definition dom_qT { CC : lC0system } { X1 X2 : B_carrier_from_C CC } ( inn : T_dom X1 X2 ) :
  ( pr1 ( qT inn ) ) = T_from_C CC _ _ inn :=
  idpath _ . 


(** **** Operation T_ext and the inductive property of operation T *)


Notation T_ext_from_C := ( T_fun.T_ext ( T_from_C _ ) ) .

Definition qT_ext { CC : lC0system } { X1 X2 : B_carrier_from_C CC } ( inn : T_ext_dom X1 X2 ) :
  mor_to X2 .
Proof.
  intros. refine ( mor_to_constr _ ) . 
  destruct (ovab_choice (pr2 inn)) as [ isab | iseq ] .
  apply ( pr1 ( qT ( T_dom_constr ( T_ext_dom_gt0 inn ) isab ) ) ) . 

  apply X1 .

  destruct (ovab_choice (pr2 inn)) as [ isab | iseq ] .
  apply ( pr2 ( qT ( T_dom_constr ( T_ext_dom_gt0 inn ) isab ) ) ) . 

  apply (( pX X1 ) ;; ( id_to_mor ( ! iseq ) ) ) . 

Defined.

Definition dom_qT_ext { CC : lC0system } { X1 X2 : B_carrier_from_C CC } ( inn : T_ext_dom X1 X2 ) :
  ( pr1 ( qT_ext inn ) ) = T_ext_from_C inn :=
  idpath _ . 


Lemma qT_as_q_of_f { CC : lC0system } { X1 X2 : B_carrier_from_C CC } ( inn : T_dom X1 X2 ) :
  qT inn = q_of_f ( T_dom_gt0_2 inn ) ( qT_ext ( T_dom_to_T_ext_dom_ft inn ) ) . 
Proof.
  intros.
  unfold qT . 
  assert ( eq : ll X2 - ll (ft X1)  = S ( ll ( ft X2 ) - ll ( ft X1 ) ) ) .
  rewrite ( ll_ft X2 ) . 
  rewrite natminuscomm .
  change  ( ll X2 - ll (ft X1) = 1 + ( ll X2 - ll ( ft X1 ) - 1 ) ) .  
  rewrite <- natassocpmeq . 
  simpl . rewrite natminuseqn . 
  apply idpath . 

  apply gth0_to_geh1 . 
  apply minusgth0 . 
  apply ( T_dom_gth inn ) .
  
  rewrite ( qn_to_qsm _ _ _ eq ) .
  rewrite qsn_strict .
  unfold qT_ext .
  set ( gt0_1 := (natgehgthtrans (ll X2) (S (ll (ft X2) - ll (ft X1))) 0
        (qsn_new_gtn (natminuslehn (ll X2) (ll (ft X1))) eq)
        (natgthsn0 (ll (ft X2) - ll (ft X1))))).
  change ((natgehgthtrans (ll X2) (S (ll (ft X2) - ll (ft X1))) 0
        (qsn_new_gtn (natminuslehn (ll X2) (ll (ft X1))) eq)
        (natgthsn0 (ll (ft X2) - ll (ft X1))))) with gt0_1 .
  assert ( int : gt0_1 = (T_dom_gt0_2 inn) ) .  
  apply ( proofirrelevance _ ( pr2 ( _ > _ ) ) ) .
  
  rewrite int .
  destruct ( ovab_choice (pr2 (T_dom_to_T_ext_dom_ft inn)) ) as [ isab | iseq ] .  unfold qT .
  rewrite ( qn_equals_qn ( C0_isaset_Ob CC ) _ ( idpath (ll (ft X2) - ll (ft X1))) _
                         (natminuslehn (ll (ft X2)) (ll (ft X1))) _ (! ( isabove_to_isover isab))).
  apply idpath .

  assert ( int' : (qn (pX X1) (ll (ft X2) - ll (ft X1))
        (ll_ft_gtn (qsn_new_gtn (natminuslehn (ll X2) (ll (ft X1))) eq))
        (ftn_ft (ll (ft X2) - ll (ft X1)) X2 @
                qsn_new_eq (! ( isabove_to_isover ( T_dom_isabove inn))) eq)) =
                   (mor_to_constr (pX X1;; id_to_mor (! iseq)))) . 
  assert ( eq0 : (ll (ft X2) - ll (ft X1)) = 0 ) . 
  rewrite iseq . 
  apply natminusnn .
  apply q0 .

  change ( q_of_mor_to (T_dom_gt0_2 inn)
     (qn (pX X1) (ll (ft X2) - ll (ft X1))
        (ll_ft_gtn (qsn_new_gtn (natminuslehn (ll X2) (ll (ft X1))) eq))
        (ftn_ft (ll (ft X2) - ll (ft X1)) X2 @
         qsn_new_eq (! ( isabove_to_isover (T_dom_isabove inn))) eq)) =
   q_of_mor_to (T_dom_gt0_2 inn) (mor_to_constr (pX X1;; id_to_mor (! iseq))) ). 
  rewrite int' . 
  apply idpath . 

Defined.


Definition T_from_C_as_f_star { CC : lC0system } { X1 X2 : B_carrier_from_C CC } ( inn : T_dom X1 X2 ) :
  T_from_C CC X1 X2 inn = f_star ( T_dom_gt0_2 inn ) ( qT_ext ( T_dom_to_T_ext_dom_ft inn ) ) :=
  maponpaths pr1 ( qT_as_q_of_f inn ) .




 



  

(** ***** Constructing operation S *)


Definition S_from_C ( CC : lC0system ) : S_ops_type ( B_carrier_from_C CC ) .
Proof.
  intros.
  unfold S_ops_type.
  intros r X inn . 
  set ( Y := ft ( dd r ) ) . set ( A := dd r ) . change _ with ( Tilde_from_C CC ) in r . 
  set ( f := r : Y --> A ) .
  set ( n := ll X - ll A ) .
  assert ( e : ftn n X = A ) . 
  set ( isov := inn : isover X A ) . 
  unfold isover in isov . 
  apply ( ! isov ) . 

  assert ( gtn : ll X >= n ) . apply natminuslehn .

  apply ( fn_star f n gtn e ) .

Defined.





Lemma S_ax1a_from_C { CC : lC0system } : S_ax1a_type ( S_from_C CC ) .
Proof.
  intros.
  unfold S_ax1a_type.
  intros .
  unfold S_from_C . 
  assert ( eq : ll Y - ll (dd r)  = S ( ll ( ft Y ) - ll ( dd r ) ) ) .
  rewrite ( ll_ft Y ) . 
  rewrite natminuscomm .
  change  ( ll Y - ll (dd r) = 1 + ( ll Y - ll ( dd r ) - 1 ) ) .  
  rewrite <- natassocpmeq . 
  simpl . rewrite natminuseqn . 
  apply idpath . 

  apply gth0_to_geh1 . 
  apply minusgth0 . 
  apply ( S_dom_gth inn ) .


  rewrite ( fn_star_to_fsm_star _ _ _ eq ) .
  rewrite fsn_strict . 
  rewrite ( @ft_f_star CC ).
  unfold fn_star . 
  apply ( maponpaths pr1 ) .  apply qn_equals_qn . 
  apply C0_isaset_Ob .

  apply idpath . 
  
Defined.
  

Lemma S_ax1b_from_C ( CC : lC0system ) : S_ax1b_type ( S_from_C CC ) .
Proof.
  intros.
  unfold S_ax1b_type . 
  intros .
  refine ( isabove_constr _ _ ) .
  unfold S_from_C . 
  rewrite (@ll_fn_star CC) .
  rewrite <- ( natplusr0 (ll (ft (dd r)))) . 
  apply natgthandplusl .
  apply minusgth0 . 
  apply ( isabove_gth inn ) . 

  unfold S_from_C . apply isover_fn_star . 

Defined.


Lemma S_ax0_from_C ( CC : lC0system ) : S_ax0_type ( S_from_C CC ) . 
Proof.
  intros.
  unfold S_ax0_type . 
  intros X1 X2 inn .
  unfold S_from_C . 
  rewrite ( @ll_fn_star CC ) . 
  rewrite ll_ft .
  rewrite natpluscomm . rewrite <- natminusinter . apply idpath . 

  apply ( natgthtogeh _ _ ( isabove_gth inn ) ) . 

  apply gth0_to_geh1 . 
  apply ll_dd_from_C . 

Defined.



(** **** Morphism qS *)



Definition Tilde_B_from_C ( CC : lC0system ) := Tilde ( B_carrier_from_C CC ) .

Definition Tilde_B_from_C_to_Tilde_from_C { CC : lC0system } ( r : Tilde_B_from_C CC ) :
  Tilde_from_C CC := r .
Coercion  Tilde_B_from_C_to_Tilde_from_C : Tilde_B_from_C >-> Tilde_from_C . 

Definition qS { CC : lC0system } { r : Tilde_B_from_C CC  } { X : B_carrier_from_C CC }
           ( inn : S_dom r X ) :
  mor_to X :=
  qn r (ll X - ll (dd r)) (natminuslehn (ll X) (ll (dd r)))
     (! ( isabove_to_isover (  inn) ) ).

Definition dom_qS { CC : lC0system } { r : Tilde_B_from_C CC } { X : B_carrier_from_C CC }
           ( inn : S_dom r X ) :
  ( pr1 ( qS inn ) ) = S_from_C CC _ _ inn :=
  idpath _ . 






(** **** Operation S_ext and the inductive property of operation S *)


Notation S_ext_from_C := ( S_ext ( S_from_C _ ) ) .

Definition qS_ext { CC : lC0system } { r : Tilde_B_from_C CC } { X : B_carrier_from_C CC }
           ( inn : S_ext_dom r X ) : mor_to X .
Proof.
  intros. refine ( mor_to_constr _ ) . 
  destruct (ovab_choice inn) as [ isab | iseq ] .
  apply ( pr1 ( qS isab ) ) . 

  apply ( ft ( dd r ) ) .

  destruct (ovab_choice inn) as [ isab | iseq ] .
  apply ( pr2 ( qS isab ) ) . 

  apply ( r ;; id_to_mor ( ! iseq ) ) . 

Defined.

Definition dom_qS_ext { CC : lC0system } { r : Tilde_B_from_C CC } { X : B_carrier_from_C CC }
           ( inn : S_ext_dom r X ) : ( pr1 ( qS_ext inn ) ) = S_ext_from_C inn :=  idpath _ . 


Lemma qS_as_q_of_f { CC : lC0system } { r : Tilde_B_from_C CC } { X : B_carrier_from_C CC }
      ( inn : S_dom r X ) : qS inn = q_of_f ( isabove_gt0 inn ) ( qS_ext ( isover_ft' inn ) ) . 
Proof.
  intros.
  unfold qS . 
  assert ( eq : ll X - ll (dd r)  = S ( ll ( ft X ) - ll ( dd r ) ) ) .
  rewrite ( ll_ft X ) . 
  rewrite natminuscomm .
  change  ( ll X - ll (dd r) = 1 + ( ll X - ll ( dd r ) - 1 ) ) .  
  rewrite <- natassocpmeq . 
  simpl . rewrite natminuseqn . 
  apply idpath . 

  apply gth0_to_geh1 . 
  apply minusgth0 . 
  apply ( S_dom_gth inn ) .
  
  rewrite ( qn_to_qsm _ _ _ eq ) .
  rewrite qsn_strict .
  unfold qS_ext .
  set ( gt0_1 := (natgehgthtrans (ll X) (S (ll (ft X) - ll (dd r))) 0
        (qsn_new_gtn (natminuslehn (ll X) (ll (dd r))) eq)
        (natgthsn0 (ll (ft X) - ll (dd r))))).
  change ((natgehgthtrans (ll X) (S (ll (ft X) - ll (dd r))) 0
        (qsn_new_gtn (natminuslehn (ll X) (ll (dd r))) eq)
        (natgthsn0 (ll (ft X) - ll (dd r))))) with gt0_1 .
  assert ( int : gt0_1 = (isabove_gt0 inn) ) .  
  apply ( proofirrelevance _ ( pr2 ( _ > _ ) ) ) .
  
  rewrite int .
  destruct ( ovab_choice (isover_ft' inn) ) as [ isab | iseq ] .  unfold qS .
  rewrite ( qn_equals_qn ( C0_isaset_Ob CC ) _ ( idpath (ll (ft X) - ll (dd r))) _
                         (natminuslehn (ll (ft X)) (ll (dd r))) _ (! ( isabove_to_isover isab))).
  apply idpath .

  assert ( int' : (qn (r) (ll (ft X) - ll (dd r))
        (ll_ft_gtn (qsn_new_gtn (natminuslehn (ll X) (ll (dd r))) eq))
        (ftn_ft (ll (ft X) - ll (dd r)) X @
                qsn_new_eq (! ( isabove_to_isover (  inn))) eq)) =
                   (mor_to_constr (r;; id_to_mor (! iseq)))) . 
  assert ( eq0 : (ll (ft X) - ll (dd r)) = 0 ) . 
  rewrite iseq . 
  apply natminusnn .
  apply q0 .

  change ( q_of_mor_to (isabove_gt0 inn)
     (qn (r) (ll (ft X) - ll (dd r))
        (ll_ft_gtn (qsn_new_gtn (natminuslehn (ll X) (ll (dd r))) eq))
        (ftn_ft (ll (ft X) - ll (dd r)) X @
         qsn_new_eq (! ( isabove_to_isover ( inn))) eq)) =
   q_of_mor_to (isabove_gt0 inn) (mor_to_constr (r;; id_to_mor (! iseq))) ). 
  rewrite int' . 
  apply idpath . 

Defined.


Definition S_from_C_as_f_star { CC : lC0system } { r : Tilde_B_from_C CC } { X : B_carrier_from_C CC }
           ( inn : S_dom r X ) :
  S_from_C CC r X inn = f_star ( isabove_gt0 inn ) ( qS_ext ( isover_ft' inn ) ) :=
  maponpaths pr1 ( qS_as_q_of_f inn ) .



      


(** **** Constructing operation Tt *)


Definition Tt_from_C ( CC : lCsystem ) : Tt_ops_type ( B_carrier_from_C CC ) .
Proof .
  intros.
  unfold Tt_ops_type.
  intros X r inn . change _ with ( Tilde_from_C CC ) in r . 
  unfold Tilde . 
  simpl . 
  unfold Tilde_B_from_C . 
  refine ( tpair _ _ _ ) . 
  exact ( T_from_C CC _ _ inn ) . 

  split.
  rewrite (@T_ax0_from_C CC) . 
  apply natgthsn0 .

  rewrite  T_from_C_as_f_star . 
  set ( f := qT_ext (T_dom_to_T_ext_dom_ft inn)).
  assert ( eq : ( pr2 f ) = ftf ( f ;; r ) ) . 
  unfold ftf . 
  rewrite <- assoc . 
  change (( pr2 f) = f;; (r;; pX (dd_from_C r))).  rewrite ( Ob_tilde_over_eq r ) . 
  rewrite id_right . 
  apply idpath .

  change (f_star (T_dom_gt0_2 inn) f) with (f_star (T_dom_gt0_2 inn) ( pr2 f)).
  rewrite eq . 
  apply sf . 

Defined.


Lemma Tt_ax1_from_C ( CC : lCsystem ) : Tt_ax1_type ( T_from_C CC ) ( Tt_from_C CC ) .
Proof.
  intros. 
  unfold Tt_ax1_type . 
  intros .
  apply idpath .

Defined.

  
(** **** Constructing operation St *)



Definition St_from_C ( CC : lCsystem ) : St_ops_type ( B_carrier_from_C CC ) .
Proof .
  intros.
  unfold St_ops_type.
  intros s r inn . change _ with ( Tilde_from_C CC ) in r . 
  unfold Tilde . 
  simpl . 
  unfold Tilde_B_from_C . 
  refine ( tpair _ _ _ ) . 
  exact ( S_from_C CC _ _ inn ) . 

  split.
  rewrite (@S_ax0_from_C CC) . 
  set ( int := S_dom_gt1 inn ) .
  apply minusgth0 . apply int . 

  rewrite  S_from_C_as_f_star . 
  set ( f := qS_ext (isover_ft' inn)).
  assert ( eq : ( pr2 f ) = ftf ( f ;; r ) ) . 
  unfold ftf . 
  rewrite <- assoc . 
  change (( pr2 f) = f;; (r;; pX (dd_from_C r))).  rewrite ( Ob_tilde_over_eq r ) . 
  rewrite id_right . 
  apply idpath .

  change (f_star (isabove_gt0 inn) f) with (f_star (isabove_gt0 inn) ( pr2 f)).
  rewrite eq . 
  apply sf . 

Defined.


Lemma St_ax1_from_C ( CC : lCsystem ) : St_ax1_type ( S_from_C CC ) ( St_from_C CC ) .
Proof.
  intros. 
  unfold St_ax1_type . 
  intros .
  apply idpath .

Defined.


(** *** The units structure dlt *)


Definition dlt_from_C ( CC : lCsystem ) : dlt_ops_type ( B_carrier_from_C CC ) .
Proof.
  intros . 
  unfold dlt_ops_type . 
  intros X gt0 . 
  split with (f_star gt0 (ftf (identity X))).
  split.
  rewrite ll_f_star . 
  apply natgthsn0 . 

  apply ( sf gt0 ( identity X ) ) . 

Defined.



Definition dlt_ax0_from_C ( CC : lCsystem ) : dlt_ax0_type ( dlt_from_C CC ) .
Proof.
  intros.
  unfold dlt_ax0_type.
  intros.
  change ( dd ( _ ) ) with (f_star gt0 (ftf (identity X))) . 
  change (ll (f_star gt0 (ftf (identity X))) = 1 + ll X).
  rewrite ll_f_star . 
  apply idpath . 

Defined.




Lemma dlt_ax1_from_C ( CC : lCsystem ) : dlt_ax1_type ( T_from_C CC ) ( dlt_from_C CC ) . 
Proof.
  intros.
  unfold dlt_ax1_type . 
  intros . 
  change ( dd ( dlt_from_C CC X gt0 ) ) with (f_star gt0 (ftf (identity X))). 
  assert ( eq : ftf ( identity X ) = pX X ) .  
  unfold ftf. apply id_left.
  
  rewrite eq .
  unfold T_from_C . 
  assert ( eq' : ll X - ll ( ft X ) = S 0 ) . 
  rewrite ll_ft .
  rewrite <- natassocmpeq . 
  rewrite natminusnn . 
  apply idpath . 

  apply isreflnatgeh . 

  apply ( gth0_to_geh1 gt0 ) . 

  rewrite ( fn_star_to_fsm_star _ _ _ eq' ) .
  rewrite fsn_strict.
  simpl .
  assert ( eq'' : id_to_mor (! qsn_new_eq (! isover_X_ftX X) eq') = identity _ ) .
  assert ( eq''' : (! qsn_new_eq (! isover_X_ftX X) eq') = idpath _ ) .
  apply C0_isaset_Ob . 

  rewrite eq'''.
  apply idpath .

  change (pX X;; id_to_mor (! qsn_new_eq (! isover_X_ftX X) eq')) with
  (pX X;; id_to_mor (! qsn_new_eq (! isover_X_ftX X) eq')) . 

  rewrite eq'' . 

  rewrite id_right . 

  assert ( eq''' : gt0 = (natgehgthtrans (ll X) 1 0
        (qsn_new_gtn (natminuslehn (ll X) (ll (ft X))) eq') 
        (natgthsn0 0)) ). apply proofirrelevance . apply ( pr2 ( _ > _ ) ) . 

  rewrite eq''' . 
  apply idpath . 
  
Defined.

  




  


(** *** Packaging everything together and constructing an l-B0-system from an l-C-system. *)


Definition T_layer_0_from_C ( CC : lC0system ) : T_layer_0 ( B_carrier_from_C CC ) :=
  tpair _ ( T_from_C CC ) ( T_ax0_from_C CC ) .

Set Printing Coercions . 

Definition T_layer_from_C ( CC : lC0system )  : T_layer ( B_carrier_from_C CC ) .
Proof.
  intros.
  split with ( T_layer_0_from_C CC ) .

  split.
  apply T_ax1a_from_C . 

  apply T_ax1b_from_C.

Defined.


Definition S_layer_0_from_C ( CC : lC0system ) : S_layer_0 ( B_carrier_from_C CC ) :=
  tpair _ ( S_from_C CC ) ( S_ax0_from_C CC ) .

Set Printing Coercions . 

Definition S_layer_from_C ( CC : lC0system )  : S_layer ( B_carrier_from_C CC ) .
Proof.
  intros.
  split with ( S_layer_0_from_C CC ) .

  split.
  apply S_ax1a_from_C . 

  apply S_ax1b_from_C. 

Defined.


Definition Tt_layer_0_from_C ( CC : lCsystem ) : Tt_layer_0 ( B_carrier_from_C CC ) .
Proof.
  intros.
  split with ( Tt_from_C CC ) . 
  apply ( Tt_ax1_to_Tt_ax0 ( T_ax0_from_C CC ) ( Tt_ax1_from_C CC ) ) .

Defined.


  
Definition Tt_layer_from_C ( CC : lCsystem ) : Tt_layer ( T_from_C CC ) .
Proof.
  intros.
  split with ( Tt_from_C CC ) .

  apply Tt_ax1_from_C .

Defined.

Definition St_layer_from_C ( CC : lCsystem ) : St_layer ( S_from_C CC ) .
Proof.
  intros.
  split with ( St_from_C CC ) .

  apply St_ax1_from_C .

Defined.

Definition St_layer_0_from_C ( CC : lCsystem ) : St_layer_0 ( B_carrier_from_C CC ) .
Proof.
  intros.
  split with ( St_from_C CC ) . 
  apply ( St_ax1_to_St_ax0 ( S_ax0_from_C CC ) ( St_ax1_from_C CC ) ) .

Defined.



Definition prelBsystem_non_unital_from_C ( CC : lCsystem ) : prelBsystem_non_unital .
Proof.
  intros.
  split with ( B_carrier_from_C CC ) .

  apply ( dirprodpair 
            ( dirprodpair ( T_layer_0_from_C CC ) ( Tt_layer_0_from_C _ ) )
            ( dirprodpair ( S_layer_0_from_C CC ) ( St_layer_0_from_C _ ) ) ) .
  
Defined.




Definition lB0_non_unital_from_C ( CC : lCsystem ) : lB0system_non_unital  .
Proof.
  intros.
  split with ( prelBsystem_non_unital_from_C CC ) .
  
  split .
  split.
  split .
  apply T_ax1a_from_C .

  apply T_ax1b_from_C .

  apply Tt_ax1_from_C .

  split.
  split . 
  apply S_ax1a_from_C .

  apply  S_ax1b_from_C .

  apply St_ax1_from_C . 

Defined.



Definition dlt_layer_0_from_C ( CC : lCsystem ) : dlt_layer_0 ( B_carrier_from_C CC ) .
Proof .
  intros.
  split with ( dlt_from_C CC ) . 

  apply dlt_ax0_from_C . 

Defined.


  
Definition dlt_layer_from_C ( CC : lCsystem ) : dlt_layer ( T_from_C CC ) .
Proof.
  intros.
  split with ( dlt_layer_0_from_C CC ) .

  apply ( dlt_ax1_from_C CC ) .

Defined.


Definition lB0_from_C ( CC : lCsystem ) : lB0system :=
  tpair _ ( lB0_non_unital_from_C CC ) ( dlt_layer_from_C CC ) .


  
  
(* End of the file lC_to_lB0_systems.v *)