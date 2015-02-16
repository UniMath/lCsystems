(** ** lCsystems by Vladimir Voevodsky,

started Dec. 4, 2014, continued Jan. 22, 2015, Feb. 11, 2015 

We refer below to the paper "Subsystems and regular quotients of C-systems"
by V. Voevodsky as "Csubsystems".

The definition of an lC-system given below does not require that the types of objects or morphisms
of the underlying precategory form a set. It also does not require the
proporties of the identity morphisms but does require associativity. 

*)

Require Export Foundations.hlevel2.hnat .
Require Export RezkCompletion.precategories.
Require Export lBsystems.ltowers.

Unset Automatic Introduction.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

Local Notation "f ;; g" := (compose f g)(at level 50).

 

Definition mor_from { C : precategory_ob_mor } ( X : C ) :=
  total2 ( fun A : C => X --> A ) .

Definition mor_from_pr2 { C : precategory_ob_mor } ( X : C ) :
  forall f : mor_from X , precategory_morphisms X ( pr1 f ) := pr2 .  
Coercion mor_from_pr2 : mor_from >-> precategory_morphisms  . 

Definition mor_from_constr { C : precategory_ob_mor } { X A : C } ( f : X --> A ) :
  mor_from X := tpair _ _ f . 

Definition mor_to { C : precategory_ob_mor } ( X : C ) :=
  total2 ( fun A : C => A --> X ) .

Definition mor_to_pr2 { C : precategory_ob_mor } ( X : C ) :
  forall f : mor_to X , precategory_morphisms ( pr1 f ) X := pr2 .  
Coercion mor_to_pr2 : mor_to >-> precategory_morphisms  . 

Definition mor_to_constr { C : precategory_ob_mor } { X A : C } ( f : A --> X ) :
  mor_to X := tpair ( fun A : C => A --> X ) _ f . 



(** To precategories *)


(* Definition wide_comp { C : precategory_data } { X Y Y' Z : C }
           ( f : X --> Y ) ( g : Y' --> Z ) ( e : Y = Y' ) : X --> Z :=
  ( transportf ( fun A : C => ( X --> A ) ) e f ) ;; g  . *)


(** *** The C0-systems

The following sequence of definitions is a formalization of Definition 2.1 in Csubsystems *)

(** **** The carrier of an lC0 -system 

as a precategory whose objects for a pointed hSet-ltower with the additional structure of
the canonical projections pX : X --> ft X . *)



(** **** l-tower precategories *)


Definition ltower_precat := total2 ( fun C : precategory => ltower_str C ) . 

Definition ltower_precat_to_ltower ( CC : ltower_precat ) : ltower :=
  tpair ( fun C : UU => ltower_str C ) ( pr1 CC ) ( pr2 CC ) .
Coercion ltower_precat_to_ltower : ltower_precat >-> ltower .

Definition ltower_precat_pr1 : ltower_precat -> precategory := pr1 .
Coercion ltower_precat_pr1 : ltower_precat >-> precategory .

Definition ltower_precat_and_p :=
  total2 ( fun CC : ltower_precat  => forall X : CC , X --> ft X ) .

Definition ltower_precat_and_p_pr1 : ltower_precat_and_p -> ltower_precat := pr1 . 
Coercion ltower_precat_and_p_pr1 : ltower_precat_and_p >-> ltower_precat . 
                                                          
Definition pX { CC : ltower_precat_and_p } ( X : CC ) : X --> ft X := pr2 CC X .


(** **** Some constructions *)


Definition ftf { CC : ltower_precat_and_p } { X Y : CC } ( f : X --> Y ) : X --> ft Y :=
  f ;; pX Y . 

Definition Ob_tilde_rel { CC : ltower_precat_and_p  } ( X : CC ) :=
  total2 ( fun r : ft X --> X => r ;; ( pX X ) = identity ( ft X ) ) .

Definition Ob_tilde_rel_to_mor_to { CC : ltower_precat_and_p } ( X : CC ) ( r : Ob_tilde_rel X ) :
  mor_to X := mor_to_constr ( pr1 r ) .
Coercion Ob_tilde_rel_to_mor_to : Ob_tilde_rel >-> mor_to . 

Definition Ob_tilde_rel_to_mor_from { CC : ltower_precat_and_p  } ( X : CC ) ( r : Ob_tilde_rel X ) :
  mor_from ( ft X ) := mor_from_constr ( pr1 r ) .
Coercion Ob_tilde_rel_to_mor_from : Ob_tilde_rel >-> mor_from .


(** **** Pointed ltower precategories *)


Definition pltower_precat_and_p :=
  total2 ( fun CC : ltower_precat_and_p => ispointed CC ) .

Definition pltower_precat_and_p_pr1 : pltower_precat_and_p ->
                                             ltower_precat_and_p := pr1 .
Coercion pltower_precat_and_p_pr1 : pltower_precat_and_p >->
                                             ltower_precat_and_p.

Definition pltower_precat_and_p_to_pltower : pltower_precat_and_p -> pltower :=
  fun X => pltower_constr ( pr2 X ) . 
Coercion pltower_precat_and_p_to_pltower : pltower_precat_and_p >-> pltower .


(** **** l-C0-system data *)


Definition q_data_type ( CC : ltower_precat_and_p ) := 
  forall ( X Y : CC ) ( gt0 : ll X > 0 ) ( f : Y --> ft X ) , mor_to X . 
Identity Coercion from_q_data_type : q_data_type >-> Funclass .  


Definition lC0system_data := total2 ( fun CC : pltower_precat_and_p => q_data_type CC ) .

Definition lC0system_data_pr1 : lC0system_data -> pltower_precat_and_p  := pr1 .
Coercion lC0system_data_pr1 : lC0system_data >-> pltower_precat_and_p .


Definition q_of_f { CC : lC0system_data }  
           { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ) : mor_to X :=
  pr2 CC _ _ gt0 f . 

Definition f_star { CC : lC0system_data }  
           { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ) : CC := 
  pr1 ( q_of_f gt0 f ) . 


(** **** Properties on l-C0-system data 

that later become axioms of an lC0-system. The numbering of the conditions below is according to 
the Csubsystems paper.

The conditions 1-3 are consequences of the definition of a pointed l-tower (pltower) *)
           

Definition C0ax4_type ( CC : pltower_precat_and_p ) :=
  forall X : CC , iscontr ( X --> cntr CC ) . 

Definition C0ax5a_type ( CC : lC0system_data ) :=
  forall ( X Y : CC ) ( gt0 : ll X > 0 ) ( f : Y --> ft X ) , ll ( f_star gt0 f ) > 0  .

Definition C0ax5b_type ( CC : lC0system_data ) :=
  forall ( X Y : CC ) ( gt0 : ll X > 0 ) ( f : Y --> ft X ) , ft ( f_star gt0 f ) = Y .

(** A construction needed to formulate further properties of the C0-system data. *)

Definition C0ax5b_mor { CC : lC0system_data } ( ax5b : C0ax5b_type CC )
           { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ) :
  ft ( f_star gt0 f ) --> Y :=
  transportf ( fun A : CC => ft ( f_star gt0 f ) --> A ) ( ax5b X Y gt0 f ) ( identity _ ) . 

(** The description of properties continues *)

Definition C0ax5c_type { CC : lC0system_data }
           ( ax5b : C0ax5b_type CC ) := 
  forall ( X Y : CC ) ( gt0 : ll X > 0 ) ( f : Y --> ft X ) , 
    pX ( f_star gt0 f ) ;; ( ( C0ax5b_mor ax5b gt0 f ) ;; f ) = ( q_of_f gt0 f ) ;; ( pX X ) . 

Definition C0ax6_type ( CC : lC0system_data ) :=
  forall ( X : CC ) ( gt0 : ll X > 0 ) ,
    q_of_f gt0 ( identity ( ft X ) ) = mor_to_constr ( identity X ) . 

Definition C0ax7_type { CC : lC0system_data } 
  ( ax5a : C0ax5a_type CC ) ( ax5b : C0ax5b_type CC ) :=
  forall ( X Y Z : CC ) ( gt0 : ll X > 0 ) ( f : Y --> ft X ) ( g : Z --> ft ( f_star gt0 f ) ) ,
    mor_to_constr ( ( q_of_f ( ax5a _ _ gt0 f ) g ) ;; ( q_of_f gt0 f ) ) =
    q_of_f gt0 ( g ;; ( ( C0ax5b_mor ax5b gt0 f ) ;; f ) ) . 



(** **** The type of l-C0-systems *)


Definition lC0system :=
  total2 ( fun CC : lC0system_data =>
             dirprod ( C0ax4_type CC )
                     ( total2 ( fun axs : dirprod ( C0ax5a_type CC )
                                                  ( total2 ( fun ax5b : C0ax5b_type CC =>
                                                               C0ax5c_type ax5b ) ) => 
                                  dirprod ( C0ax6_type CC )
                                          ( C0ax7_type ( pr1 axs ) ( pr1 ( pr2 axs ) ) ) ) ) ) .

Definition lC0system_pr1 : lC0system -> lC0system_data := pr1 .
Coercion lC0system_pr1 : lC0system >-> lC0system_data . 

Definition C0ax4 ( CC : lC0system ) : C0ax4_type CC := pr1 ( pr2 CC ) . 

Definition C0ax5a { CC : lC0system } { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ) :
  ll ( f_star gt0 f ) > 0 := pr1 ( pr1 ( pr2 ( pr2 CC ) ) ) X Y gt0 f .

Definition C0ax5b { CC : lC0system } { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ) :
  ft ( f_star gt0 f ) = Y := pr1 ( pr2 ( pr1 ( pr2 ( pr2 CC )))) X Y gt0 f .

Definition C0emor { CC : lC0system } { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ) :
  ft ( f_star gt0 f ) --> Y := C0ax5b_mor ( @C0ax5b CC ) gt0 f . 


Definition C0ax5c { CC : lC0system }
           { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ) : 
  pX ( f_star gt0 f ) ;; ( ( C0emor gt0 f ) ;; f ) =
  ( q_of_f gt0 f ) ;; ( pX X ) :=
  pr2 ( pr2 ( pr1 ( pr2 ( pr2 CC )))) X Y gt0 f . 


Definition C0ax6 { CC : lC0system } { X : CC } ( gt0 : ll X > 0 ) :
  q_of_f gt0 ( identity ( ft X ) ) = mor_to_constr ( identity X ) :=
  pr1 ( pr2 ( pr2 ( pr2 CC ))) X gt0 .

Definition C0ax6a { CC : lC0system } { X : CC } ( gt0 : ll X > 0 ) :
  f_star gt0 ( identity ( ft X ) ) = X :=
  maponpaths pr1 ( C0ax6 gt0 ) . 

Definition C0ax7 { CC : lC0system }
           { X Y Z : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ) ( g : Z --> ft ( f_star gt0 f ) ) :
  mor_to_constr ( ( q_of_f ( C0ax5a gt0 f ) g ) ;; ( q_of_f gt0 f ) ) =
  q_of_f gt0 ( g ;; ( ( C0emor gt0 f ) ;; f ) ) :=
  pr2 ( pr2 ( pr2 ( pr2 CC ))) X Y Z gt0 f g . 

Definition C0ax7a { CC : lC0system }
           { X Y Z : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ) ( g : Z --> ft ( f_star gt0 f ) ) :
  f_star ( C0ax5a gt0 f ) g = f_star gt0 ( g ;; ( ( C0emor gt0 f ) ;; f ) ) :=
  maponpaths pr1 ( C0ax7 gt0 f g ) . 







(** *** The l-C-systems *)


(** **** l-C-system data *) 

Definition sf_type ( CC : lC0system_data ) :=
  forall ( Y X : CC ) ( gt0 : ll X > 0 ) ( f : Y --> X ) , Ob_tilde_rel ( f_star gt0 ( ftf f ) ) .

(* ??? Need canonical structures to productively use the following concept???

Definition lCsystem_data := total2 ( fun CC : lC0system_data => sf_type CC ) .

Definition lCsystem_data_constr { CC : lC0system_data } ( sf0 : sf_type CC ) : lCsystem_data :=
  tpair _ _ sf0 . 

Definition lCsystem_data_pr1 : lCsystem_data -> lC0system_data := pr1 .
Coercion lCsystem_data_pr1 : lCsystem_data >-> lC0system_data .

Definition sf { CC : lCsystem_data } { Y X : CC } ( gt0 : ll X > 0 ) ( f : Y --> X ) :
  Ob_tilde_rel ( f_star gt0 ( ftf f ) ) :=
  pr2 CC Y X gt0 f . 

*)




(** **** Properties on l-C-system data 

that later become axioms of l-C-systems. *)


Definition sf_ax1_type { CC : lC0system } ( sf0 : sf_type CC ) :=
  forall ( Y X : CC ) ( gt0 : ll X > 0 ) ( f : Y --> X ) ,
    ( C0emor gt0 ( ftf f ) ) ;; f = ( sf0 _ _ gt0 f ) ;; ( q_of_f gt0 ( ftf f ) ) .

Lemma sf_ax2_type_l1 { CC : lC0system } ( sf0 : sf_type CC )
      { Y Y' U : CC } ( gt0 : ll U > 0 )
      ( g : Y' --> ft U ) ( f : Y --> f_star gt0 g ) :
  f_star (C0ax5a gt0 g) (ftf f) = f_star gt0 (ftf (f ;; q_of_f gt0 g)) .
Proof.
  intros. 
  assert ( int1 : f_star (C0ax5a gt0 g) (ftf f) =
                  f_star gt0 ( ( ftf f ) ;; ( ( C0emor gt0 g ) ;; g ) ) ) .
  apply C0ax7a.

  assert ( int2 : f_star gt0 ( ( ftf f ) ;; ( ( C0emor gt0 g ) ;; g ) ) =
                  f_star gt0 ( f ;; ( ( pX _ ) ;; ( ( C0emor gt0 g ) ;; g ) ) ) ) . 
  unfold ftf . rewrite <- assoc . 
  apply idpath . 

  assert ( int3 : f_star gt0 ( f ;; ( ( pX _ ) ;; ( ( C0emor gt0 g ) ;; g ) ) ) =
                  f_star gt0 ( f ;; ( ( q_of_f gt0 g ) ;; ( pX U ) ) ) ) .
  unfold ftf . rewrite C0ax5c .
  apply idpath . 

  assert ( int4 : f_star gt0 ( f ;; ( ( q_of_f gt0 g ) ;; ( pX U ) ) ) =
                  f_star gt0 (ftf (f ;; q_of_f gt0 g)) ) .
  unfold ftf . rewrite assoc .
  apply idpath . 

  exact ( ( int1 @ int2 ) @ ( int3 @ int4 ) ) . 

Defined.

Definition sf_ax2_type { CC : lC0system } ( sf : sf_type CC ) :=
  forall ( Y Y' U : CC ) ( gt0 : ll U > 0 )
         ( g : Y' --> ft U ) ( f : Y --> f_star gt0 g ) ,
     transportf Ob_tilde_rel  (sf_ax2_type_l1 sf gt0 g f ) ( sf Y _ ( C0ax5a gt0 g ) f ) =
     sf Y _ gt0 ( f ;; q_of_f gt0 g ) .  


(** **** The definition of the type of l-C-systems *)


Definition lCsystem :=
  total2 ( fun CC : lC0system =>
             total2 ( fun sf0 : sf_type CC =>
                        dirprod ( sf_ax1_type sf0 ) ( sf_ax2_type sf0 ) ) ) .

Definition lCsystem_pr1 : lCsystem -> lC0system := pr1 .
Coercion lCsystem_pr1 : lCsystem >-> lC0system .

(* Definition lCsystem_to_lCsystem_data ( CC : lCsystem ) : lCsystem_data :=
  @lCsystem_data_constr CC ( pr1 ( pr2 CC ) ) .
Coercion lCsystem_to_LCsystem_data : lCsystem >-> lCsystem_data . *)

Definition sf { CC : lCsystem } { Y X : CC } ( gt0 : ll X > 0 ) ( f : Y --> X ) :
  Ob_tilde_rel ( f_star gt0 ( ftf f ) ) := pr1 ( pr2 CC ) _ _ gt0 f . 
  
Definition sf_ax1 { CC : lCsystem } { Y X : CC } ( gt0 : ll X > 0 ) ( f : Y --> X ) :
  ( C0emor gt0 ( ftf f ) ) ;; f = ( sf gt0 f ) ;; ( q_of_f gt0 ( ftf f ) ) :=
  pr1 ( pr2 ( pr2 CC ) ) Y X gt0 f . 

Definition sf_ax2 { CC : lCsystem } { Y Y' U : CC } ( gt0 : ll U > 0 )
           ( g : Y' --> ft U ) ( f : Y --> f_star gt0 g ) :
  transportf Ob_tilde_rel  (sf_ax2_type_l1 ( @sf CC ) gt0 g f ) ( sf ( C0ax5a gt0 g ) f ) =
  sf gt0 ( f ;; q_of_f gt0 g ) :=
  pr2 ( pr2 ( pr2 CC ) ) Y Y' U gt0 g f .


                                
(** *** Operations fn_star and qn_of_f *)

Definition qn { CC : lC0system_data } { Y A : CC } ( f : Y --> A ) ( n : nat ) 
           { X : CC } ( eq : ftn n X = A )  : mor_to X .
Proof.
  intros until n . 
  induction n as [ | n IHn ] .
  intros . 
  change _ with ( X = A ) in eq . 
  rewrite eq . apply ( mor_to_constr f ) . 

  intros .
  
  assert ( eq' : ftn n ( ft X ) = A ) . rewrite ftn_ft . apply eq . 

  set ( qn := IHn ( ft X ) eq' ) .
  destruct ( natgehchoice _ _ ( natgehn0 ( ll X ) ) ) as [ gt0 | eq0 ] .  
  
  apply ( @q_of_f CC _ _ gt0 qn ) .

  assert ( eq'' : ft X = X ) . apply ( ftX_eq_X eq0 ) .
  rewrite <- eq'' . 
  apply qn . 

Defined.

Definition fn_star { CC : lC0system_data } { Y A : CC } ( f : Y --> A ) ( n : nat ) 
           { X : CC } ( eq : ftn n X = A ) : CC := pr1 ( qn f n eq ) .


(* Definition fun_star_s { CC : lCsystem } { Y A : CC } ( f : Y --> A ) ( n : nat ) 
           { X : CC } ( eq : ftn n X = A ) ( r : Ob_tilde *)





(* End of the file lCsystems.v *)