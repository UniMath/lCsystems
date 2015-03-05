(** ** Comparison on morphisms.  

by Vladimir Voevodsky, split from the file lBsystems.lBsystems_to_precategories.v  on
March 3, 2015 

Comparing morphisms of the lB0-system defined by an lC-system with morphisms 
of the original lC-system.

*)

Unset Automatic Introduction.

Require Export lCsystems.lC_to_lB0.
Require Export lBsystems.lB_to_precat.







(** *** Function from morphisms of the lB0-system associated with a C-system

- to morphisms of the original C-system *)


(** **** Construction of a function from iterated_sections to morphisms *)


(** An object of Tilde_dd X in the case when the lB0-system is of the form lB0_from_C has 
the following form:

(( Y , ( ( gt0 : ll Y > 0 ) , ( ( s : ft Y --> Y ) , ( eq : s ;; ( pX Y ) = indenity ( ft Y ) ) ) ) ) ,
( eq' : Y = X ))

this explains the complex sequences of projections in the proofs below. *) 



Definition Tilde_dd_to_mor { CC : lCsystem } { X : CC } ( s : @Tilde_dd ( lB0_from_C CC ) X ) :
  ft X --> X .
Proof.
  intros .
  set ( s' := pr1 s : @Tilde ( lB0_from_C CC ) ) .
  set ( s_eq := pr2 s : dd s' = X ) .
  set ( s_mor := pr1 ( pr2 ( pr2 s') ) : ft ( dd s' ) --> dd s' ) .
  rewrite s_eq in s_mor . 
  exact s_mor.

Defined.




  
Definition Tilden_dd_to_mor { CC : lCsystem } { m : nat } { Z : CC }
           ( itrs : @Tilden_dd ( lB0_from_C CC ) m Z ) : ftn m Z --> Z .
Proof.
  intros until m . 
  induction m as [ | m IHm ] . 
  intros . 
  apply ( identity Z ) .

  intros . 
  destruct m as [ | m ] .
  apply ( Tilde_dd_to_mor itrs ) .

  set ( s1 := pr1 itrs : Tilde_dd _ ) . 
  set ( s1' := pr1 s1 : Tilde _  ) .
  set ( s_eq := pr2 s1 : dd s1' = ftn ( S m ) Z ) .
  set ( gt0 := pr1 ( pr2 s1' ) :  ll ( dd s1' ) > 0 ) .
  assert ( gt : ll Z > S m ) . rewrite s_eq in gt0 . rewrite ll_ftn in gt0 .
  apply ( minusgth0inv _ _ gt0 ) .
  
  
  set ( s_mor := pr1 ( pr2 ( pr2 s1' ) ) : ft ( dd s1' ) --> dd s1' ) .
  set ( inn := (@Tilden_dd_inn ( lB0_from_C CC ) _ _ s1)).
  set ( sm := pr2 itrs : Tilden_dd ( S m ) (@S_op ( lB0_from_C CC ) s1 Z inn)) .
  assert ( le' : S m <= ll ( @S_op ( lB0_from_C CC ) s1 Z inn) ) . 
  rewrite ll_S . apply ( natgthtominus1geh gt ). 
  

  assert ( f := IHm (@S_op ( lB0_from_C CC ) s1 Z inn) sm ) . 

  assert ( qn_from_S : @S_op ( lB0_from_C CC ) s1 Z inn --> Z ) .  
  unfold S_op. 
  exact ( qn s_mor (ll Z - ll (dd s1)) _ _ ) .

  assert ( eq : ftn ( S ( S m ) ) Z = ftn ( S m ) ( @S_op ( lB0_from_C CC ) s1 Z inn ) ) . 
  assert ( isov : isover ( ( @S_op ( lB0_from_C CC ) s1 Z inn ) ) ( ft ( dd s1 ) ) ) .
  exact ( @S_ax1b ( lB0_from_C CC ) _ _ _ ) . 
  
  unfold isover in isov . change (Tilde_dd_pr1 s1) with s1' in isov . 
  rewrite s_eq in isov . 
  change ( ftn ( S ( S m ) ) Z ) with ( ft ( ftn ( S m ) Z ) ) .  
  refine ( isov @ _ ) . 
  assert ( eq_in_nat : ll (@S_op ( lB0_from_C CC ) s1 Z inn) - ll (ft (ftn ( S m ) Z)) = ( S m ) ) .
  rewrite ( @S_ax0 ( lB0_from_C CC )).
  rewrite ll_ft . 
  rewrite ll_ftn .
  rewrite natmiusmius1mminus1 . 
  apply natminusmmk .

  apply ( natgthtogeh _ _ gt ) .

  apply ( natgthgehtrans _ _ _ gt ( natgehn0 _ ) ).
 
  apply minusgth0 . apply gt.   

  apply ( maponpaths ( fun n => ftn n _ ) eq_in_nat ) .

  apply ( ( id_to_mor eq ) ;; f ;; qn_from_S ) . 

Defined.



(** **** Construction of the (horizontal) projection from ( Tj X A Y ) to Y *)



Definition hor_proj_ft_case { CC : lCsystem } ( X Z : CC ) ( gt0 : ll X > 0 ) :
  @Tprod ( lB0_from_C CC ) X Z --> @Tprod ( lB0_from_C CC ) ( ft X ) Z .
Proof .
  intros.
  rewrite ( @Tprod_compt ( lB0_from_C CC ) _ _ gt0 ) .
  unfold T_ext .   
  unfold T_fun.T_ext .
  change ( ll X > 0 ) with ( ll ( X : ( lB0_from_C CC ) ) > 0 ) in gt0 . 
  set ( ch := ovab_choice (pr2 (T_ext_dom_constr gt0 (isover_Tprod (ft ( X  : ( lB0_from_C CC ) )) Z)))) .
  destruct ch as [ isab | iseq ] . 
  exact ( pr2 ( qn _ _ _ _ ) )  . 

  change (Tprod _ _) with (Tprod (ft ( X  : ( lB0_from_C CC ) )) Z) . rewrite iseq . 
  apply pX . 

Defined.

  
Definition hor_proj_int { CC : lCsystem } ( X Y Z : CC ) ( isov : isover X Y ) :
  @Tprod ( lB0_from_C CC ) X Z --> @Tprod ( lB0_from_C CC ) Y Z :=
  isover_ind
            ( fun X0 Y0 => @Tprod ( lB0_from_C CC ) X0 Z --> @Tprod ( lB0_from_C CC ) Y0 Z )
            ( fun X0 => identity _ )
            ( fun X0 gt0 => hor_proj_ft_case X0 Z gt0 )
            ( fun X0 Y0 f g => f ;; g ) X Y isov .


Definition hor_proj_cntr_case { CC : lCsystem } ( Y : CC ) : 
  @Tprod ( lB0_from_C CC ) ( cntr CC ) Y --> Y .
Proof.
  intros .
  unfold Tprod . 
  unfold Tprod_over . 
  unfold Tprod_fun . 
  unfold T_fun.Tj_fun.
  rewrite (@isover_ind_compt0 ( lB0_from_C CC )). 
  simpl . 
  apply identity . 

Defined.


Definition hor_proj { CC : lCsystem } ( X Y : CC ) : 
  @Tprod ( lB0_from_C CC ) X Y --> Y .
Proof.
  intros .
  assert ( int1 : @Tprod ( lB0_from_C CC ) X Y --> @Tprod ( lB0_from_C CC ) ( cntr CC ) Y ) .
  apply hor_proj_int . 
  exact ( @isover_cntr ( lB0_from_C CC ) X ) . 

  assert ( int2 :  @Tprod ( lB0_from_C CC ) ( cntr CC ) Y --> Y ) . apply hor_proj_cntr_case .

  exact ( int1 ;; int2 ) . 

Defined.



(** **** The function from morphisms of the lB0-system constrcuted from a C-system to morphisms
of the C-system. *)


Definition Mor_lB0_from_C_to_Mor { CC : lCsystem } ( X Y : CC )
           ( f : @Mor_from_B ( lB0_from_C CC ) X Y ) : X --> Y . 
Proof .
  intros .
  unfold Mor_from_B in f .
  set ( int1 := Tilden_dd_to_mor f ) .
  assert ( eq : ftn ( ll Y ) ( @Tprod ( lB0_from_C CC ) X Y ) = X ) . 
  set ( isov := @isover_Tprod ( lB0_from_C CC ) X Y ) . 
  unfold isover in isov . 
  assert ( eq'' : ftn (ll (@Tprod ( lB0_from_C CC ) X Y) - ll X) (@Tprod ( lB0_from_C CC ) X Y) =
                  ftn (ll Y) (@Tprod ( lB0_from_C CC ) X Y) ) .
  rewrite ll_Tprod . 
  rewrite natpluscomm .
  rewrite plusminusnmm . 
  apply idpath . 

  exact ( ( ! eq'' ) @ ( ! isov ) ) . 

  change (ftn (ll Y) (Tprod _ _ )) with (ftn (ll Y) (@Tprod ( lB0_from_C CC ) X Y)) in int1 . 
  rewrite eq in int1 . 

  assert ( int2 := hor_proj X Y ) . 

  exact ( int1 ;; int2 ) . 

Defined.


(** *** The function from the morphisms of an lC-system to the morphisms of the associated 
lB0-system. *)


(** **** Sections of the iterated canonical projection to the Tilden_dd *)


Definition sec_pX_to_Tilde_dd { CC : lCsystem }
           ( X : CC ) ( le : 1 <= ll X ) ( s : sec_pX X ) : @Tilde_dd ( lB0_from_C CC ) X .
Proof.
  intros.
  refine ( tpair _ _ _ ).
  split with X.  
  split with ( geh1_to_gth0 le ).
  unfold Ob_tilde_over.
  split with ( pr1 s ). 
  apply ( pr2 s ).
  apply idpath.

Defined.

 
Lemma pre_sec { CC : lCsystem }
      ( m : nat ) ( X : CC ) ( le : S m  <= ll X ) ( s : sec_pnX ( S m ) X ) : sec_pX ( ftn m X ). 
Proof.
  intros.
  split with ((pr1 s) ;; ( pnX m X ) ). 
  rewrite <- assoc.
  destruct m as [ | m ].
  rewrite id_left. 
  apply ( pr2 s ). 

  apply ( pr2 s ).

Defined.










  


(*Definition sec_pnX_to_Tilden_dd { CC : lCsystem }
           ( m : nat ) ( X : CC ) ( le : m <= ll X ) ( s : sec_pnX m X ) :
  @Tilden_dd ( lB0_from_C CC ) m X .
Proof .
  intros until m . induction m as [ | m IHm ] .
  intros . simpl .  apply tt . 

  intros . 
  simpl . 
  destruct m as [ | m ] . 
  apply sec_pX_to_Tilde_dd. 

  apply le.

  apply s. 

  set ( s11 := s ;; ( pnX ( S m ) X ) ).
  assert ( eq11 : s11 ;; pX ( ftn ( S m ) X ) =  identity _ ). 
  unfold s11.
  rewrite <- assoc. 
  exact ( pr2 s ).   

  refine ( tpair _ _ _ ).  
  unfold Tilde_dd.
  unfold Tilde. 
  simpl.
  unfold Tilde_from_C. refine ( tpair _ _ _ ). 
  split with ( ftn ( S m ) X ).
  split.
  rewrite ll_ftn.
  apply minusgth0. 
  apply ( natgehgthtrans _ _ _ le ( natgthsnn _ ) ). 

  apply ( tpair _ s11 eq11 ). 

  apply idpath . 

  unfold Tilden_dd.
  destruct m as [ | m ].
  simpl.

  
  unfold S_op. 
  unfold S_fun.S_op.
*)



  
  

(* End of the file Mor_comparison.v *)