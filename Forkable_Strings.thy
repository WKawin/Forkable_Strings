theory Forkable_Strings imports Main "~~/src/HOL/List" begin

text "We will use True as 1 and False as 0 in characteristic strings; we might think about each bool
value answers to the question 'is this slot controlled by an adversarial player?'."

datatype nattree = Empty | Node nat "nattree list"
(*datatype nattree = Node nat "nattree list" *)

fun lt_nat_tree :: "nat \<Rightarrow> nattree \<Rightarrow> bool" where
  "lt_nat_tree n Empty = True" 
| "lt_nat_tree n (Node m _) = (n < m)"
 
lemma lt_nat_tree_lt [simp]: "(n < m) \<longleftrightarrow> lt_nat_tree n (Node m l)"
  by simp
    
lemma lt_nat_tree_ge [simp]: "(n \<ge> m) \<longleftrightarrow> \<not> lt_nat_tree n (Node m l)"
  by auto
  
fun increasing_tree :: "nattree \<Rightarrow> bool" where
  "increasing_tree Empty = True"
| "increasing_tree (Node _ []) = True" 
| "increasing_tree (Node n l) = (\<forall>x \<in> set l. increasing_tree x \<and> lt_nat_tree n x)"

lemma increasing_tree_empty_branch_list [simp]: "increasing_tree (Node n [])"
  by simp

lemma increasing_tree_ind [simp] : "(\<forall>x \<in> set l. increasing_tree x \<and> lt_nat_tree n x) \<longleftrightarrow> increasing_tree (Node n l)"
  by (smt increasing_tree.elims(2) increasing_tree.elims(3) length_greater_0_conv length_pos_if_in_set nattree.distinct(1) nattree.inject)     

definition ListMax :: "nat list \<Rightarrow> nat" where
  "ListMax l = foldr max l 0"

lemma max_of_the_list_0 [simp]: "ListMax [] = 0"
  by (simp add: ListMax_def)

lemma max_of_the_list [simp]: "\<forall>x \<in> set l. x \<le> ListMax l"    
  proof (induction l)
    case Nil
    then show ?case 
      by auto 
  next
    case (Cons a l)
    have "ListMax (Cons a l) = max a (ListMax l)"
      using ListMax_def by auto
    have "ListMax l \<le> ListMax (Cons a l) \<and> a \<le> ListMax (Cons a l)"
      by (simp add: \<open>ListMax (a # l) = max a (ListMax l)\<close>)
    then show ?case
      using Cons.IH by auto 
  qed
    
fun height_branch :: "nattree \<Rightarrow> nat" where
  "height_branch Empty = 0"
| "height_branch (Node _ l) = 1 + ListMax (map height_branch l)"

lemma height_branch_empty_list [simp]: "height_branch (Node n []) = 1"
  by simp

lemma height_branch_lt [simp]: "\<forall>x \<in> set l. height_branch x < height_branch (Node n l)"
  by (simp add: le_imp_less_Suc)
  
fun height :: "nattree \<Rightarrow> nat" where
  "height Empty = 0"
| "height (Node n bl) = ListMax (map height_branch bl)"

lemma height_empty_list [simp]: "height (Node n []) = 0"
  by simp

lemma height_ge [simp]: "\<forall>x \<in> set l. height_branch x \<le> height (Node n l)"
  by auto
 
fun depth_branch :: "nat \<Rightarrow> nattree \<Rightarrow> nat" where
  "depth_branch m Empty = 0"
| "depth_branch m (Node n l) = (if m = n then 1 else 
                                      (case ListMax (map (depth_branch m) l) of 
                                            0 \<Rightarrow> 0 | 
                                            Suc n \<Rightarrow> Suc (Suc n)))"

lemma depth_branch_eq [simp] : "depth_branch m (Node m l) = 1"
  by simp

lemma listmax_0 [simp]: "(\<forall> x \<in> set l. f x = 0) \<longrightarrow> ListMax (map f l) = 0"
proof (induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  have "ListMax (map f (Cons a l)) = max (f a) (ListMax (map f l))"
    using ListMax_def by auto
  then have "(f a = 0) \<and> (\<forall> x \<in> set l. f x = 0) \<longrightarrow> ListMax (map f (Cons a l))  = 0"
    using Cons.IH by linarith
  then show ?case
    by simp 
qed  

lemma depth_branch_empty_branch_list [simp]: "depth_branch m (Node n []) = of_bool (m = n)"    
proof (cases "m = n")
  case True
  then show ?thesis by simp 
next
  case False
  then show ?thesis by auto
qed
  
lemma depth_branch_ne_nf [simp]: 
"(\<forall> x \<in> set l. depth_branch m x = 0) \<and> m \<noteq> n \<longrightarrow> depth_branch m (Node n l) = 0" 
by simp
  
fun depth :: "nattree \<Rightarrow> nat \<Rightarrow> nat" where
  "depth _ 0 = 0" 
| "depth Empty n = 0"
| "depth (Node n bl) m = ListMax (map (depth_branch m) bl)"
    
lemma depth_root_ge [simp] : "m > 0 \<longrightarrow> (\<forall>x \<in> set l. depth_branch m x  \<le> depth (Node n l) m)"
  using gr0_conv_Suc image_eqI by auto   

(* I put ' here because we want getFrom started at 1 not 0*)
fun getFrom' :: "bool list \<Rightarrow> nat \<Rightarrow> bool" where
  "getFrom' [] n = True"
| "getFrom' (x#xs) 0 = x"
| "getFrom' (x#xs) (Suc n) = getFrom' xs n"  

(*  
fun H' :: "bool list \<Rightarrow> nat \<Rightarrow> nat set" where
  "H' [] _ = {}"
| "H' (x#xs) n = (if x then (H' xs (Suc n)) else {n} \<union> (H' xs (Suc n)))"

definition H :: "bool list \<Rightarrow> nat set" where
  "H l = H' l 1"
*)
  
definition H :: "bool list \<Rightarrow> nat set" where
  "H l = {x. \<not> getFrom' (False#l) x}"

lemma H_0 [simp]: "0 \<in> H l"
  by (simp add: H_def)
  
lemma getFrom_suc_eq_H [simp]: "\<not> getFrom' l x \<longleftrightarrow> Suc x \<in> H l"
  using H_def by auto 

fun ListSum :: "nat list \<Rightarrow> nat" where
  "ListSum l = foldr plus l 0"
  
(*no prunning as we don't yet have an increasing tree in argument, but can improve it later*)
fun count_node :: "nat \<Rightarrow> nattree \<Rightarrow> nat" where
  "count_node _ Empty = 0"
| "count_node m (Node n bl) = (of_bool (m = n)) + ListSum (map (count_node m) bl)"

lemma count_node_empty_branch_list [simp] : "count_node m (Node n []) = of_bool (m = n)" by simp

definition unique_node :: "nattree \<Rightarrow> nat \<Rightarrow> bool" where
  "unique_node t n = (count_node n t = 1)"
  
fun unique_nodes_by_nat_set :: "nattree \<Rightarrow> nat set \<Rightarrow> bool" where
 "unique_nodes_by_nat_set t s = (\<forall>x \<in> s. unique_node t x)"
  
definition uniqueH_tree :: "nattree \<Rightarrow> bool list \<Rightarrow> bool" where
  "uniqueH_tree t l =  unique_nodes_by_nat_set t (H l)"    

lemma uniqueH_tree_in_imp_l [simp]: "\<forall> x \<in> H l. uniqueH_tree t l \<longrightarrow> unique_node t x"
  using uniqueH_tree_def by auto 
    
lemma uniqueH_tree_in_imp_r [simp]: "(\<forall> x \<in> H l. unique_node t x) \<longrightarrow> uniqueH_tree t l"
  using uniqueH_tree_def unique_nodes_by_nat_set.simps by blast
    
fun max_node :: "nattree \<Rightarrow> nat" where
  "max_node Empty = 0"
| "max_node (Node n bl) = ListMax (n # (map max_node bl))"

lemma ListSum_0 [simp] :"(\<forall>x \<in> set l. x = 0) \<longrightarrow> ListSum l = 0" 
  proof (induction l)
    case Nil
    then show ?case by simp
  next
    case (Cons a l)
    then show ?case
      by simp 
  qed
  
lemma max_node_max [simp]: "\<forall> m. max_node t < m  \<longrightarrow> count_node m t = 0"
  proof (induction t)
    case Empty
    then show ?case
      by simp 
  next
    case (Node x1 x2)
    have "max_node (Node x1 x2) = ListMax (x1 # (map max_node x2))" 
      by simp
    then have "\<forall>x \<in> set x2. max_node x \<le> max_node (Node x1 x2) \<and> x1 \<le> max_node (Node x1 x2)"
      by simp
    then have "\<forall>x. \<forall>y \<in> set x2 . max_node (Node x1 x2)< x \<longrightarrow> max_node y < x \<and> x1 < x"
      using le_less_trans by blast  
    then have "\<forall>x. \<forall>y \<in> set x2 . max_node (Node x1 x2)< x \<longrightarrow> count_node x y = 0"
      by (simp add: Node.IH)
    then have "\<forall>x. max_node (Node x1 x2)< x \<longrightarrow> count_node x (Node x1 x2) =  ListSum (map (count_node x) x2)"
      by (smt \<open>max_node (Node x1 x2) = ListMax (x1 # map max_node x2)\<close> 
add.commute add_cancel_left_right count_node.simps(2) less_irrefl_nat less_le_trans list.set_intros(1) max_of_the_list of_bool_def)
    then show ?case
      using ListSum_0 \<open>\<forall>x. \<forall>y\<in>set x2. max_node (Node x1 x2) < x \<longrightarrow> count_node x y = 0\<close> by auto 
  qed
  
fun increasing_depth_H :: "nattree \<Rightarrow> bool list \<Rightarrow> bool" where 
  "increasing_depth_H t l = (\<forall>x \<in> H l. \<forall>y \<in> H l. x < y \<longrightarrow> depth t x < depth t y)"

fun root_label0 :: "nattree \<Rightarrow> bool" where
  "root_label0 Empty = False"
| "root_label0 (Node 0 _) = True"
| "root_label0 (Node (Suc n) _) = False"
  
text "F |- w" 
fun isFork :: "bool list \<Rightarrow> nattree \<Rightarrow> bool" where
  "isFork w F = ((length w \<ge> max_node F) 
               \<and> (increasing_tree F) 
               \<and> (uniqueH_tree F w) 
               \<and> (increasing_depth_H F w)
               \<and> root_label0 F)"

lemma isFork_max_not_exceed [simp] : "isFork w F \<longrightarrow> length w \<ge> max_node F" by simp

lemma isFork_root_0 [simp] : "isFork w F \<longrightarrow> root_label0 F" by simp

lemma isFork_increasing_tree [simp] : "isFork w F \<longrightarrow> increasing_tree F"
  using isFork.simps by blast 
    
lemma isFork_uniqueH_tree [simp] : "isFork w F \<longrightarrow> (\<forall>x \<in> H w. unique_node F x)"
  by (meson isFork.elims(2) uniqueH_tree_in_imp_l)

lemma isFork_increasing_depth_H [simp] : "isFork w F \<longrightarrow> (\<forall> x \<in> H w. \<forall> y \<in> H w. x < y \<longrightarrow> depth F x < depth F y)"
  by (meson increasing_depth_H.elims(2) isFork.elims(2))    
    
(*Definition 4.11*)
fun flatTree :: "nattree \<Rightarrow> bool" where
  "flatTree Empty = False"
| "flatTree (Node _ []) = True"
| "flatTree (Node 0 l) = (Suc (Suc 0) \<le> 
foldr ((\<lambda>x.(\<lambda>y.(if x = (height (Node 0 l)) then Suc y else y)))) (map height_branch l) 0)"
| "flatTree (Node (Suc n) l) = False"
  
definition isForkable :: "bool list \<Rightarrow> bool" where
  "isForkable w = (\<exists>F. (isFork w F) \<and> flatTree F)"

(*Definition 4.13 is really tricky as we have to traverse F and F' whether it holds that F \<subseteq> F' at 
the same time*)
fun order_map :: "(nat \<Rightarrow> 'b \<Rightarrow> 'c list) \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> 'c list" where
  "order_map f [] _ = []"   
| "order_map f (x#xs) n = f n x @ (order_map f xs (Suc n))"
  
fun order_map_disjoint :: "(nat \<Rightarrow> 'b \<Rightarrow> 'c list) \<Rightarrow> nat  \<Rightarrow> 'b list \<Rightarrow> ('c list) list" where
  "order_map_disjoint f _ [] = []"   
| "order_map_disjoint f n (x#xs) = f n x # (order_map_disjoint f (Suc n) xs)" 

function firstN_R :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "firstN_R i n = (if i \<ge>  n then [] else i#(firstN_R (Suc i) n))"
   apply auto[1] by blast
    
termination firstN_R 
  apply (relation "measure (\<lambda>(i,n). n - i)")
  apply simp
  by simp  
  
definition firstN :: "nat \<Rightarrow> nat list" where
  "firstN n = firstN_R 0 n" 
    
function tinelist_nat :: "nat \<Rightarrow> nattree \<Rightarrow> (nat list) list" where
  "tinelist_nat _ Empty = [[]]"
| "tinelist_nat m (Node _ []) = [[m]]"
| "tinelist_nat m (Node _ (x#xs)) = map (Cons m) 
(foldr append (map (\<lambda>(n,t). tinelist_nat n t) (zip (firstN (length (x#xs))) (x#xs))) [])"
  apply (metis depth_branch.cases neq_Nil_conv)
  by auto
  
fun total_node :: "nattree \<Rightarrow> nat" where
  "total_node Empty = 0"
| "total_node (Node n l) = Suc (ListSum (map total_node l))"

lemma total_nod_dec [simp] : "\<forall>x \<in> set l. total_node x < total_node (Node n l)"
proof (induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case by auto
qed
    
lemma [simp]: "(a, b) \<in> set (zip (firstN (Suc (length xs))) (x # xs)) \<Longrightarrow>
       total_node b < Suc (total_node x + foldr op + (map total_node xs) 0)"
using total_nod_dec set_zip_rightD by force

termination tinelist_nat
  apply (relation "measure (\<lambda>(n,nt). total_node nt)")
  apply auto
  done
   
fun tinelist :: "nattree \<Rightarrow> (nat list) list" where
  "tinelist Empty = []" 
| "tinelist (Node 0 l) = (foldr append (map (\<lambda>(n,t). tinelist_nat n t) (zip (firstN (length l)) l)) [])"
| "tinelist (Node (Suc n) l) = []" (*not in our concern*)
  
fun getLabelFromTine :: "nattree \<Rightarrow> nat list \<Rightarrow> nat list" where 
  "getLabelFromTine Empty l = []"
| "getLabelFromTine _ [] = []"
| "getLabelFromTine (Node _ l) (x#xs) = (case hd (drop x l) of 
                                               Empty \<Rightarrow> [] | (*it runs out of nodes before we can trace down all paths*)
                                               Node n _ \<Rightarrow> n # getLabelFromTine (hd (drop x l)) xs)"  

fun isPrefix_lists :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "isPrefix_lists [] _ = True"
| "isPrefix_lists (l#ls) [] = False"
| "isPrefix_lists (l#ls) (r#rs) = ((l=r) \<and> isPrefix_lists ls rs)"
  
definition isPrefix_tines :: "nattree \<Rightarrow> nattree \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
 "isPrefix_tines nt1 nt2 t1 t2 = 
(isPrefix_lists t1 t2 \<and> isPrefix_lists (getLabelFromTine nt1 t1) (getLabelFromTine nt2 t2))  "

definition isPrefix_trees :: "nattree \<Rightarrow> nattree \<Rightarrow> bool" where
  "isPrefix_trees nt1 nt2 = 
    (\<forall>t1. (\<forall>t2. ListMem t1 (tinelist nt1) \<and> ListMem t2 (tinelist nt2) \<longrightarrow> isPrefix_tines nt1 nt2 t1 t2))"

definition isPrefix_forks :: "bool list \<Rightarrow> bool list \<Rightarrow> nattree \<Rightarrow> nattree \<Rightarrow> bool" where
  "isPrefix_forks w1 w2 nt1 nt2 = 
    (isFork w1 nt1 \<and> isFork w2 nt2 \<and> isPrefix_lists w1 w2 \<and> isPrefix_trees nt1 nt2)"
  
inductive ListOfEmpty :: "nattree list \<Rightarrow> bool" where
  Nil : "ListOfEmpty []"
| Cons : "ListOfEmpty l \<Longrightarrow> ListOfEmpty (Empty#l)"
  
(*Definition 4.14*)
(*there is a problem about how we know this is the end of a tine*)
fun closedFork_Hgiven :: "nattree \<Rightarrow> nat set \<Rightarrow> bool" where
  "closedFork_Hgiven Empty _ = True"
| "closedFork_Hgiven (Node n l) h = (if ListOfEmpty l 
                                     then (n \<in> h) 
                                     else foldr conj (map (\<lambda>x. closedFork_Hgiven x h) l) True)"
  
definition closedFork :: "nattree \<Rightarrow> bool list \<Rightarrow> bool" where
  "closedFork t w = closedFork_Hgiven t (H w)"
  
(*as I define tines using nat list, length of tines is easily defined by length of list - 1*)  
(*from Definition 4.16, gap reserve and reach depend on a fork and a characteristic string*)
  
definition gap :: "nattree \<Rightarrow> nat list \<Rightarrow> nat" where
  "gap nt tine = height nt - (length tine)"
  
definition reserve :: "bool list \<Rightarrow> nat list \<Rightarrow> nat" where
  "reserve w labeledTine = foldr (\<lambda>x.(plus (of_bool x)))  (drop (ListMax labeledTine) w) 0"

definition reach :: "nattree \<Rightarrow> bool list \<Rightarrow> nat list \<Rightarrow> nat" where
  "reach nt w tine = reserve w tine - gap nt tine"
  
(*\<lambda> and \<mu> from Definition 4.16*)
  
definition lambda :: "nattree \<Rightarrow> bool list \<Rightarrow> nat" where
  "lambda t w = ListMax (map (reach t w) (tinelist t)) "

fun crosslist :: "'a list \<Rightarrow> 'a list \<Rightarrow> (('a, 'a) prod) list" where
  "crosslist [] _ = []"
| "crosslist (x#xs) ys = (map (Pair x) ys) @ (crosslist xs ys) "

fun cross_all_pair' :: "('a list) list \<Rightarrow>  ('a list,(('a, 'a) prod) list) prod" where
  "cross_all_pair' [] = ([],[])"
| "cross_all_pair' (x#xs) = (x @ fst (cross_all_pair' xs), 
(crosslist x (fst (cross_all_pair' xs))) @ snd (cross_all_pair' xs))"

definition cross_all_pair :: "('a list) list \<Rightarrow>  (('a, 'a) prod) list" where
  "cross_all_pair l = snd (cross_all_pair' l)"

fun list_of_disjoint_edged_tines :: "nattree \<Rightarrow> ((nat list, nat list) prod) list" where
  "list_of_disjoint_edged_tines Empty = []"
| "list_of_disjoint_edged_tines (Node n l) 
   = cross_all_pair (order_map_disjoint (\<lambda>x. map (Cons x))  0 (map tinelist l))"

definition margin :: "nattree \<Rightarrow>  bool list \<Rightarrow> nat" where
  "margin t w = foldr (\<lambda>(a,b).max (min (reach t w a) (reach t w b))) (list_of_disjoint_edged_tines t) (0 - (height t))"

proposition proposition_4_17 : "isForkable w \<longleftrightarrow> (\<exists> F.(isFork w F \<and> margin F w \<ge> 0))" 
 sorry

definition lambda_of_string :: "bool list \<Rightarrow> nat" where   
  "lambda_of_string w = (GREATEST t. (\<exists>F.(isFork w F \<and> closedFork F w \<and> t = lambda F w)))"

definition margin_of_string :: "bool list \<Rightarrow> nat" where
  "margin_of_string w = (GREATEST t. (\<exists>F.(isFork w F \<and> closedFork F w \<and> t = margin F w)))"

definition m :: "bool list \<Rightarrow> (nat, nat) prod" where
  "m w = (lambda_of_string w, margin_of_string w)"
  
lemma lemma_4_18 : "(m [] = (0,0)) \<and> 
  (\<forall> w. ((length w > 0) \<longrightarrow> ( 
    (m (w @ [True]) = (lambda_of_string w + 1, margin_of_string w + 1)) 
     \<and>   ((lambda_of_string w > margin_of_string w) \<and> (margin_of_string w = 0)
          \<longrightarrow> (m (w @ [False]) = (lambda_of_string w - 1, 0)))
     \<and>   (lambda_of_string w = 0 \<longrightarrow> (m (w @ [False]) = (0, margin_of_string w - 1)))
     \<and>   (lambda_of_string w > 0 \<and> margin_of_string w \<noteq> 0 \<longrightarrow> (m (w @ [False]) 
          = (lambda_of_string w - 1, margin_of_string w - 1))))) 
\<and> (\<exists> F. (isFork w F \<and> closedFork F w  \<and> (m w = (lambda F w, margin F w)))))"
  sorry
    
end