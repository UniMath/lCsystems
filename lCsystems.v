(** lCsystems by Vladimir Voevodsky,
started Dec. 4, 2014, continued Jan. 22, 2015 *)

Require Export Foundations.hlevel2.hnat .
Require Export RezkCompletion.precategories.
Require Export lBsystems.lTowers.

Unset Automatic Introduction.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

Local Notation "f ;; g" := (compose f g)(at level 50). 

(* To precategories? *)


Definition wide_comp { C : precategory_data } { X Y Y' Z : C }
           ( f : X --> Y ) ( g : Y' --> Z ) ( e : Y = Y' ) : X --> Z :=
  ( transportf ( fun A : C => ( X --> A ) ) e f ) ;; g  . 


(** We start defining C-systems as pre-categories of the RezkCompletion together 
with the lTower structure on the collection of objects connected to each other through the 
canonical projections p : X -> ft X *)

Definition lTower_precat := total2 ( fun C : precategory => lTower_str C ) .

Definition lTower_precat_to_lTower ( CC : lTower_precat ) : lTower :=
  tpair ( fun C : UU => lTower_str C ) ( pr1 CC ) ( pr2 CC ) .
Coercion lTower_precat_to_lTower : lTower_precat >-> lTower .

Definition lTower_precat_pr1 : lTower_precat -> precategory := pr1 .
Coercion lTower_precat_pr1 : lTower_precat >-> precategory .

Definition lTower_and_p_precat :=
  total2 ( fun CC : lTower_precat  => forall X : CC , X --> ft X ) .

Definition lTower_and_p_precat_pr1 : lTower_and_p_precat -> lTower_precat := pr1 . 
Coercion lTower_and_p_precat_pr1 : lTower_and_p_precat >-> lTower_precat . 

                                                              
(* Definition ftX ( C : precategory_ob_mor ) ( ftd : ft_data C ) : C -> C := pr1 ftd . 
Coercion ftX : ft_data >-> Funclass . *)

Definition pX { CC : lTower_and_p_precat } ( X : CC ) : X --> ft X := pr2 CC X .

(* *)

Definition q_data_type ( CC : lTower_and_p_precat ) := 
  forall ( X Y : CC ) ( is : ll X > 0 ) ( f : Y --> ft X ) ,
    total2 ( fun fstarX : CC => fstarX --> X ) .   

Definition f_star { CC : lTower_and_p_precat } (qd : q_data_type CC ) 
           { X Y : CC } ( is : ll X > 0 ) ( f : Y --> ft X ) := 
  pr1 ( qd X Y is f ) . 

Definition q_of_f { CC : lTower_and_p_precat } ( qd : q_data_type CC )
           { X Y : CC } ( is : ll X > 0 ) ( f : Y --> ft X ) : f_star qd is f --> X :=
  pr2 ( qd X Y is f ) . 

Definition wide_q { CC : lTower_and_p_precat } ( qd : q_data_type CC ) 
           { X : CC } { X' Y : CC } ( is : ll X > 0 ) ( f : Y --> X' ) ( e : X' = ft X ) : 
  total2 ( fun fstarX => fstarX --> X ) :=
  qd X Y is ( transportf ( fun A : CC => ( Y --> A ) ) e f ) . 


           

(* 

A problem arises with the following definition since one of the morphisms f or 
( pX ftd ( fstar qd is f ) ) 
need to be transported along the equality fteq in order for the composition  
( pX ftd ( fstar qd is f ) ) ;; f 
to be defined. Therefore we have to use wide_comp  *) 


Definition C0sysax5a_type { CC : lTower_and_p_precat } ( qd : q_data_type CC ) :=
  forall ( X Y : CC ) ( is : ll X > 0 ) ( f : Y --> ft X ) , ll ( f_star qd is f ) > 0  .

Definition C0sysax5b_type { CC : lTower_and_p_precat } ( qd : q_data_type CC ) :=
  forall ( X Y : CC ) ( is : ll X > 0 ) ( f : Y --> ft X ) , ft ( f_star qd is f ) = Y .

Definition C0sysax5c_type { CC :  lTower_and_p_precat } { qd : q_data_type CC }
           ( ax : C0sysax5b_type qd ) := 
  forall ( X Y : CC ) ( is : ll X > 0 ) ( f : Y --> ft X ) , 
    wide_comp ( pX ( f_star qd is f ) ) f ( ax X Y is f ) = ( q_of_f qd is f ) ;; ( pX X ) . 


(* Lemma loff_star { CC : lTower_and_p_precat } { ft : ft_data CC } { l : CC -> nat } { qd : q_data_type ft l }
      ( ax2 : C0sysax2 l ft ) ( ax5a : C0sysax5a qd ) { X : CC } { Y : CC } ( is : natgth ( l X ) 0 ) ( f : Y --> ft X ) : 
  l ( f_star qd is f ) = 1 + l Y . 
Proof. intros .  admit . Qed . *)
  

(* Definition C0sysax1 { CC : UU } ( l : CC -> nat ) := iscontr ( total2 ( fun X : CC => l X = 0 ) ) . *)

(* Definition C0pt { CC : UU } { l : CC -> nat } ( ax : C0sysax1 l ) : CC := pr1 ( pr1  ax ) . *)

(* Definition C0sysax3 { CC : lTower_and_p_precat } { ft : ft_data CC } { l : CC -> nat } { ax : C0sysax1 l } :=
  ft ( C0pt ax ) = C0pt ax . *) 

(* Here it might be better to use the standard definition of being a final object *)

(* Definition C0sysax4 { CC : lTower_and_p_precat } { l : CC -> nat } { ax : C0sysax1 l } := 
  forall X : CC , iscontr ( X --> C0pt ax ) . *)

Definition C0sysax6_type { CC : lTower_and_p_precat } { qd : q_data_type CC } :=
  forall ( X : CC ) ( is : ll X > 0 ) ,
    qd _ _ is ( identity ( ft X ) ) = tpair _ X ( identity X ) . 

Definition C0sysax7_type { CC : lTower_and_p_precat } { qd : q_data_type CC } 
  ( ax5a : C0sysax5a_type qd ) ( ax5b : C0sysax5b_type qd ) :=
  forall ( X Y Z : CC ) ( is : ll X > 0 ) ( g : Z --> Y ) ( f : Y --> ft X ) , 
    qd _ _ is ( g ;; f ) = 
    let is' := ax5a _ _ is f   in
    tpair _ ( pr1 ( wide_q qd is' g ( pathsinv0 ( ax5b X Y is f ) ) ) ) 
          ( ( pr2 ( wide_q qd is' g ( pathsinv0 ( ax5b X Y is f ) ) ) ) ;; q_of_f qd is f  ) . 








(* 

Note: continue checking the definition of a C-system as a category with attributes together with additional data.

Then check the connection with categories with families of Peter Dybjer. *)




(* Let's try the definition of a category with attributes instead. 

Definition atr_data_1 ( CC : lTower_and_p_precat ) := total2 ( fun 

*)





 



(* End of the file lCsystems.v *)