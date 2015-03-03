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

Definition iter_sec_to_mor { CC : lCsystem } { m : nat } { Z : CC } { le : m <= ll Z }
           ( itrs : @iter_sec ( lB0_from_C CC ) m Z le ) : ftn m Z --> Z .
Proof.
  intros until m . 
  induction m . 
  intros . 
  apply ( identity Z ) .

  intros . 
  simpl in itrs . 
  destruct (natgehchoice m 0 (natgehn0 m)) as [ gt0 | eq0 ] .

  set ( s := pr1 itrs ) .
  set ( s_eq := pr2 ( pr1 itrs ) : dd s = ftn m Z ) .
  set ( s_mor := pr2 ( pr2 ( pr1 ( pr1 itrs ) ) ) : ft ( dd s ) --> dd s ) .
  set ( inn := (@iter_sec_inn ( lB0_from_C CC ) _ _ gt0 le s)).
  set ( le' := (@iter_sec_le ( lB0_from_C CC ) _ _ gt0 le s)).
  set ( sm := pr2 itrs : iter_sec m (@S_op ( lB0_from_C CC ) s Z inn) le') . 
  assert ( s1 := IHm (@S_op ( lB0_from_C CC ) s Z inn) le' sm ) . 

  assert ( qn_from_S : @S_op ( lB0_from_C CC ) s Z inn --> Z ) .  
  unfold S_op.
  simpl .
  unfold S_from_C . 
  exact ( qn s_mor (ll Z - ll (dd s)) _ _ ) .

  assert ( eq : ftn ( S m ) Z = ftn m ( @S_op ( lB0_from_C CC ) s Z inn ) ) . 
  assert ( isov : isover ( ( @S_op ( lB0_from_C CC ) s Z inn ) ) ( ft ( dd s ) ) ) .
  apply isabove_to_isover .  apply S_ax1b_from_C . 

  unfold isover in isov . 
  rewrite s_eq in isov . 
  change ( ftn ( S m ) Z ) with ( ft ( ftn m Z ) ) . 
  refine ( isov @ _ ) . 
  assert ( eq_in_nat : ll (@S_op ( lB0_from_C CC ) s Z inn) - ll (ft (ftn m Z)) = m ) . 
  rewrite ll_S .
  rewrite ll_ft . 
  rewrite ll_ftn .
  rewrite natmiusmius1mminus1 . 
  apply natminusmmk .

  apply ( istransnatgeh _ _ _ le ( natgehsnn _ ) ) .

  apply ( natgehgthtrans _ _ _ le ( natgthsn0 _ ) ) . 

  apply minusgth0 . apply ( natgehgthtrans _ _ _ le ( natgthsnn _ ) ) . 

  apply ( maponpaths ( fun n => ftn n _ ) eq_in_nat ) .

  apply ( ( id_to_mor eq ) ;; s1 ;; qn_from_S ) . 

  rewrite eq0 . 
  change ( ft Z --> Z ) . 
  set ( s_eq := pr2 itrs : dd itrs = Z ) .
  set ( s_mor := pr2 ( pr2 ( pr1 itrs ) ) : ft ( dd itrs ) --> dd itrs ) .
  rewrite s_eq in s_mor . 
  exact s_mor.

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
  set ( int1 := iter_sec_to_mor f ) .
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











(* End of the file Mor_comparison.v *)