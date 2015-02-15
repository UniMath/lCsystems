(** ** lCsystems by Vladimir Voevodsky,

started Dec. 4, 2014, continued Jan. 22, 2015, Feb. 11, 2015 

We refer below to the paper "Subsystems and regular quotients of C-systems"
by V. Voevodsky as "Csubsystems".

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


Definition ltower_precat := total2 ( fun C : precategory => ltower_str C ) . 

Definition ltower_precat_to_ltower ( CC : ltower_precat ) : ltower :=
  tpair ( fun C : UU => ltower_str C ) ( pr1 CC ) ( pr2 CC ) .
Coercion ltower_precat_to_ltower : ltower_precat >-> ltower .

Definition ltower_precat_pr1 : ltower_precat -> precategory := pr1 .
Coercion ltower_precat_pr1 : ltower_precat >-> precategory .

Definition ltower_and_p_precat :=
  total2 ( fun CC : ltower_precat  => forall X : CC , X --> ft X ) .

Definition ltower_and_p_precat_pr1 : ltower_and_p_precat -> ltower_precat := pr1 . 
Coercion ltower_and_p_precat_pr1 : ltower_and_p_precat >-> ltower_precat . 
                                                          
Definition pX { CC : ltower_and_p_precat } ( X : CC ) : X --> ft X := pr2 CC X .

Definition pltower_and_p_precat :=
  total2 ( fun CC : ltower_and_p_precat => ispointed CC ) .

Definition pltower_and_p_precat_pr1 : pltower_and_p_precat ->
                                             ltower_and_p_precat := pr1 .
Coercion pltower_and_p_precat_pr1 : pltower_and_p_precat >->
                                             ltower_and_p_precat.

Definition pltower_and_p_precat_to_pltower : pltower_and_p_precat -> pltower :=
  fun X => pltower_constr ( pr2 X ) . 
Coercion pltower_and_p_precat_to_pltower : pltower_and_p_precat >-> pltower . 


Definition q_data_type ( CC : ltower_and_p_precat ) := 
  forall ( X Y : CC ) ( gt0 : ll X > 0 ) ( f : Y --> ft X ) , mor_to X . 
Identity Coercion from_q_data_type : q_data_type >-> Funclass .  


Definition lC0system_data := total2 ( fun CC : pltower_and_p_precat => q_data_type CC ) .

Definition lC0system_data_pr1 : lC0system_data -> pltower_and_p_precat  := pr1 .
Coercion lC0system_data_pr1 : lC0system_data >-> pltower_and_p_precat .

Definition q_data { CC : lC0system_data }  
           { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ) : mor_to X :=
  pr2 CC _ _ gt0 f . 

Definition f_star { CC : lC0system_data }  
           { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ) : CC := 
  pr1 ( q_data gt0 f ) . 

Definition q_of_f { CC : lC0system_data }
           { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ) : f_star gt0 f --> X :=
  pr2 ( q_data gt0 f ) .



(** A construction needed for the formulation of the axioms of lC0-systems. *)


(* Definition wide_q { CC : lC0system_data }
           { X : CC } { X' Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> X' ) ( e : X' = ft X ) : 
  total2 ( fun fstarX => fstarX --> X ) :=
  (pr2 CC) X Y gt0 ( transportf ( fun A : CC => ( Y --> A ) ) e f ) . *)




(** The numbering of the axioms below is according to the Csubsystems paper

The axioms 1-3 are consequences of the definition of a pointed l-tower (pltower) *)
           

Definition C0ax4_type ( CC : pltower_and_p_precat ) :=
  forall X : CC , iscontr ( X --> cntr CC ) . 

Definition C0ax5a_type ( CC : lC0system_data ) :=
  forall ( X Y : CC ) ( gt0 : ll X > 0 ) ( f : Y --> ft X ) , ll ( f_star gt0 f ) > 0  .

Definition C0ax5b_type ( CC : lC0system_data ) :=
  forall ( X Y : CC ) ( gt0 : ll X > 0 ) ( f : Y --> ft X ) , ft ( f_star gt0 f ) = Y .

(** A construction needed to formulate further conditions on the C0-systm data. *)

Definition C0ax5b_mor { CC : lC0system_data } ( ax5b : C0ax5b_type CC )
           { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ) :
  ft ( f_star gt0 f ) --> Y :=
  transportf ( fun A : CC => ft ( f_star gt0 f ) --> A ) ( ax5b X Y gt0 f ) ( identity _ ) . 

(** The definition of conditions continues *)

Definition C0ax5c_type { CC : lC0system_data }
           ( ax5b : C0ax5b_type CC ) := 
  forall ( X Y : CC ) ( gt0 : ll X > 0 ) ( f : Y --> ft X ) , 
    pX ( f_star gt0 f ) ;; ( ( C0ax5b_mor ax5b gt0 f ) ;; f ) = ( q_of_f gt0 f ) ;; ( pX X ) . 

Definition C0ax6_type ( CC : lC0system_data ) :=
  forall ( X : CC ) ( gt0 : ll X > 0 ) ,
    q_data gt0 ( identity ( ft X ) ) = mor_to_constr ( identity X ) . 

Definition C0ax7_type { CC : lC0system_data } 
  ( ax5a : C0ax5a_type CC ) ( ax5b : C0ax5b_type CC ) :=
  forall ( X Y Z : CC ) ( gt0 : ll X > 0 ) ( f : Y --> ft X ) ( g : Z --> ft ( f_star gt0 f ) ) ,
    mor_to_constr ( ( q_of_f ( ax5a _ _ gt0 f ) g ) ;; ( q_of_f gt0 f ) ) =
    q_data gt0 ( g ;; ( ( C0ax5b_mor ax5b gt0 f ) ;; f ) ) . 



(** **** The type of lC0-systems *)


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
  q_data gt0 ( identity ( ft X ) ) = mor_to_constr ( identity X ) :=
  pr1 ( pr2 ( pr2 ( pr2 CC ))) X gt0 .

Definition C0ax6a { CC : lC0system } { X : CC } ( gt0 : ll X > 0 ) :
  f_star gt0 ( identity ( ft X ) ) = X :=
  maponpaths pr1 ( C0ax6 gt0 ) . 

Definition C0ax7 { CC : lC0system }
           { X Y Z : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ) ( g : Z --> ft ( f_star gt0 f ) ) :
  mor_to_constr ( ( q_of_f ( C0ax5a gt0 f ) g ) ;; ( q_of_f gt0 f ) ) =
  q_data gt0 ( g ;; ( ( C0emor gt0 f ) ;; f ) ) :=
  pr2 ( pr2 ( pr2 ( pr2 CC ))) X Y Z gt0 f g . 

Definition C0ax7a { CC : lC0system }
           { X Y Z : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ) ( g : Z --> ft ( f_star gt0 f ) ) :
  f_star ( C0ax5a gt0 f ) g = f_star gt0 ( g ;; ( ( C0emor gt0 f ) ;; f ) ) :=
  maponpaths pr1 ( C0ax7 gt0 f g ) . 




(** **** Some constructions for lC0-systems *)


Definition ftf { CC : ltower_and_p_precat } { X Y : CC } ( f : X --> Y ) : X --> ft Y :=
  f ;; pX Y . 


Definition Ob_tilde { CC : lC0system } ( X : CC ) :=
  total2 ( fun r : ft X --> X => r ;; ( pX X ) = identity ( ft X ) ) .

Definition Ob_tilde_to_mor_to { CC : lC0system } ( X : CC ) ( r : Ob_tilde X ) : mor_to X :=
  mor_to_constr ( pr1 r ) .
Coercion Ob_tilde_to_mor_to : Ob_tilde >-> mor_to . 

Definition Ob_tilde_to_mor_from { CC : lC0system } ( X : CC ) ( r : Ob_tilde X ) : mor_from ( ft X ) :=
  mor_from_constr ( pr1 r ) .
Coercion Ob_tilde_to_mor_from : Ob_tilde >-> mor_from . 
  


(** *** The lC-systems *)


Definition s_f_type ( CC : lC0system ) :=
  forall ( Y X : CC ) ( gt0 : ll X > 0 ) ( f : Y --> X ) , Ob_tilde ( f_star gt0 ( ftf f ) ) .

(* Definition s_f_ax1_type { CC : lC0system } ( s_f : s_f_type CC ) :=
  forall ( Y X : CC ) ( gt0 : ll X > 0 ) ( f : Y --> X ) ,
    s_f Y X gt0 f ;; pX ( f_star gt0 ( ftf f ) ) =
    transportb ( fun A => Y --> A ) ( C0ax5b gt0 ( ftf f ) ) ( identity Y ) . *)

Definition s_f_ax1_type { CC : lC0system } ( s_f : s_f_type CC ) :=
  forall ( Y X : CC ) ( gt0 : ll X > 0 ) ( f : Y --> X ) ,
    ( C0emor gt0 ( ftf f ) ) ;; f = ( s_f Y X gt0 f ) ;; ( q_of_f gt0 ( ftf f ) ) .

Lemma s_f_ax2_type_l1 { CC : lC0system } ( s_f : s_f_type CC )
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

Definition s_f_ax2_type { CC : lC0system } ( s_f : s_f_type CC ) :=
  forall ( Y Y' U : CC ) ( gt0 : ll U > 0 )
         ( g : Y' --> ft U ) ( f : Y --> f_star gt0 g ) ,
     transportf Ob_tilde  (s_f_ax2_type_l1 s_f gt0 g f ) ( s_f Y _ ( C0ax5a gt0 g ) f ) =
     s_f Y _ gt0 ( f ;; q_of_f gt0 g ) .  




(* End of the file lCsystems.v *)