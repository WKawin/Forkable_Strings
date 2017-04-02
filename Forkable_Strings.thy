theory Forkable_Strings imports Main "~~/src/HOL/List" begin

text "We will use True as 1 and False as 0 in characteristic strings; we might think about each bool
value answers to the question 'is this slot controlled by an adversarial player?'."

datatype nattree = Empty | Node nat "nattree list"
text "One reason why we don't have Leaves here is that we have to define prefixes of tines carefully 
so that we don't consider having a leaf with cannot be continue by a list of trees but instead we
can have a list of Emptys in order to extend each Empty by a tree"
  
inductive ListOfEmpty :: "nattree list \<Rightarrow> bool" where
  Nil : "ListOfEmpty []"
| Cons : "ListOfEmpty l \<Longrightarrow> ListOfEmpty (Empty#l)"
  
inductive Leaf :: "nattree \<Rightarrow> bool" where
"ListOfEmpty l \<Longrightarrow> Leaf (Node n l)" 
  
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
  
lemma increasing_tree_branch_list_of_empty [simp]: "ListOfEmpty x \<longrightarrow> increasing_tree (Node n x)"
proof (induction x)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then show ?case 
  proof (cases a)
    case Empty
    then show ?thesis
    proof -
      obtain nn :: "nattree list \<Rightarrow> nattree \<Rightarrow> nat \<Rightarrow> nattree" where
        "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> set (x1 # x0) \<and> (\<not> increasing_tree v3 \<or> \<not> lt_nat_tree x2 v3)) = (nn x0 x1 x2 \<in> set (x1 # x0) \<and> (\<not> increasing_tree (nn x0 x1 x2) \<or> \<not> lt_nat_tree x2 (nn x0 x1 x2)))"
        by moura
      then have f1: "\<forall>n na ns. (\<not> increasing_tree (Node n (na # ns)) \<or> (\<forall>nb. nb \<notin> set (na # ns) \<or> increasing_tree nb \<and> lt_nat_tree n nb)) \<and> (increasing_tree (Node n (na # ns)) \<or> nn ns na n \<in> set (na # ns) \<and> (\<not> increasing_tree (nn ns na n) \<or> \<not> lt_nat_tree n (nn ns na n)))"
        by (meson increasing_tree.simps(3))
      obtain nns :: "nattree list \<Rightarrow> nattree list" where
            f2: "\<forall>ns. (\<not> ListOfEmpty ns \<or> ns = [] \<or> ns = Empty # nns ns \<and> ListOfEmpty (nns ns)) \<and> (ListOfEmpty ns \<or> ns \<noteq> [] \<and> (\<forall>nsa. ns \<noteq> Empty # nsa \<or> \<not> ListOfEmpty nsa))"
        by (metis ListOfEmpty.simps)
      have "(Empty # x = Empty # nns (a # x)) = (x = nns (a # x))"
        by blast
      then show ?thesis
        using f2 f1 by (metis (no_types) Cons.IH Empty in_set_member increasing_tree.simps(1) lt_nat_tree.simps(1) member_rec(1) member_rec(2))
    qed 
    next
    case (Node x21 x22)
    then show ?thesis
      using ListOfEmpty.simps by blast 
  qed
    
qed
  
lemma increasing_tree_ind [simp] : "(\<forall>x \<in> set l. increasing_tree x \<and> lt_nat_tree n x) \<longleftrightarrow> increasing_tree (Node n l)"
proof -
  { fix nn :: nattree
    obtain nna :: "nattree \<Rightarrow> nat" and nnb :: "nattree \<Rightarrow> nattree" and nns :: "nattree \<Rightarrow> nattree list" and nnc :: "nattree \<Rightarrow> nattree" where
      ff1: "\<forall>n. increasing_tree n \<or> Node (nna n) (nnb n # nns n) = n \<and> nnc n \<in> set (nnb n # nns n) \<and> (\<not> increasing_tree (nnc n) \<or> \<not> lt_nat_tree (nna n) (nnc n))"
      using increasing_tree.elims(3) by moura
    have "\<forall>n ns. (n::nattree) \<notin> set ns \<or> (\<exists>nsa. n # nsa = ns) \<or> (\<exists>na nsa. na # nsa = ns \<and> n \<in> set nsa)"
      by (metis list.set_cases)
    then obtain nnsa :: "nattree \<Rightarrow> nattree list \<Rightarrow> nattree list" and nnd :: "nattree \<Rightarrow> nattree list \<Rightarrow> nattree" and nnsb :: "nattree \<Rightarrow> nattree list \<Rightarrow> nattree list" where
      ff2: "\<forall>n ns. n \<notin> set ns \<or> n # nnsa n ns = ns \<or> nnd n ns # nnsb n ns = ns \<and> n \<in> set (nnsb n ns)"
      by moura
    obtain nne :: "nat \<Rightarrow> nattree \<Rightarrow> nattree list \<Rightarrow> nattree" where
      ff3: "\<forall>n na ns. (\<not> increasing_tree (Node n (na # ns)) \<or> (\<forall>nb. nb \<notin> set (na # ns) \<or> increasing_tree nb \<and> lt_nat_tree n nb)) \<and> (nne n na ns \<in> set (na # ns) \<and> (\<not> increasing_tree (nne n na ns) \<or> \<not> lt_nat_tree n (nne n na ns)) \<or> increasing_tree (Node n (na # ns)))"
      by moura
    then have ff4: "\<forall>n na nb ns. lt_nat_tree nb n \<or> n \<notin> set (nnd na ns # nnsb na ns) \<or> \<not> increasing_tree (Node nb ns) \<or> na # nnsa na ns = ns \<or> na \<notin> set ns"
      using ff2 by metis
    { assume "nn # nnsa nn l \<noteq> l"
      { assume "\<exists>na. nn # nnsa nn l \<noteq> l \<and> increasing_tree (Node na (nnd nn l # nnsb nn l)) \<and> nn # nnsa nn l \<noteq> l \<and> increasing_tree (Node n l)"
        moreover
        { assume "\<exists>na nb. increasing_tree (Node n l) \<and> nn # nnsa nn l \<noteq> l \<and> increasing_tree (Node na (nnd nb l # nnsb nb l)) \<and> nb # nnsa nb l \<noteq> l \<and> nb \<in> set l \<and> increasing_tree (Node n l)"
          moreover
          { assume "\<exists>na nb nc. nb \<in> set l \<and> increasing_tree (Node n l) \<and> nb # nnsa nb l \<noteq> l \<and> increasing_tree (Node n l) \<and> increasing_tree (Node nc (nnd na l # nnsb na l)) \<and> na # nnsa na l \<noteq> l \<and> na \<in> set l \<and> increasing_tree (Node n l)"
            moreover
            { assume "\<exists>na nb nc ns. nb # nnsa nb ns \<noteq> ns \<and> nb \<in> set ns \<and> increasing_tree (Node n l) \<and> nn \<in> set ns \<and> increasing_tree (Node n ns) \<and> increasing_tree (Node na (nnd nc l # nnsb nc l)) \<and> nc # nnsa nc l \<noteq> l \<and> nc \<in> set l \<and> increasing_tree (Node n l)"
              then have "(nn \<notin> set l \<or> increasing_tree nn \<and> lt_nat_tree n nn) \<and> increasing_tree (Node n l) \<or> \<not> increasing_tree (Node n l) \<and> (\<exists>na. na \<in> set l \<and> (\<not> increasing_tree na \<or> \<not> lt_nat_tree n na))"
                using ff4 ff3 ff2 by (metis (no_types)) }
            ultimately have "(nn \<notin> set l \<or> increasing_tree nn \<and> lt_nat_tree n nn) \<and> increasing_tree (Node n l) \<or> \<not> increasing_tree (Node n l) \<and> (\<exists>na. na \<in> set l \<and> (\<not> increasing_tree na \<or> \<not> lt_nat_tree n na))"
              by blast }
          ultimately have "(nn \<notin> set l \<or> increasing_tree nn \<and> lt_nat_tree n nn) \<and> increasing_tree (Node n l) \<or> \<not> increasing_tree (Node n l) \<and> (\<exists>na. na \<in> set l \<and> (\<not> increasing_tree na \<or> \<not> lt_nat_tree n na))"
            by blast }
        ultimately have "(nn \<notin> set l \<or> increasing_tree nn \<and> lt_nat_tree n nn) \<and> increasing_tree (Node n l) \<or> \<not> increasing_tree (Node n l) \<and> (\<exists>na. na \<in> set l \<and> (\<not> increasing_tree na \<or> \<not> lt_nat_tree n na))"
          by blast }
      then have "(nn \<notin> set l \<or> increasing_tree nn \<and> lt_nat_tree n nn) \<and> increasing_tree (Node n l) \<or> \<not> increasing_tree (Node n l) \<and> (\<exists>na. na \<in> set l \<and> (\<not> increasing_tree na \<or> \<not> lt_nat_tree n na))"
        using ff3 ff2 ff1 by (metis (no_types) nattree.inject) }
    then have "(nn \<notin> set l \<or> increasing_tree nn \<and> lt_nat_tree n nn) \<and> increasing_tree (Node n l) \<or> \<not> increasing_tree (Node n l) \<and> (\<exists>na. na \<in> set l \<and> (\<not> increasing_tree na \<or> \<not> lt_nat_tree n na))"
      using ff3 ff1 by (metis (no_types) list.set_intros(1) nattree.inject) }
  then show ?thesis
    by auto
qed

definition ListMax :: "nat list \<Rightarrow> nat" where
  "ListMax l = foldr max l 0"

lemma ListMax_0 [simp]: "ListMax [] = 0"
  by (simp add: ListMax_def)

lemma Listmax_ge [simp]: "\<forall>x \<in> set l. x \<le> ListMax l"    
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
    
fun height :: "nattree \<Rightarrow> nat" where
  "height Empty = 0"  
| "height (Node n bl) = (if Leaf (Node n bl) then 0 else Suc (ListMax (map height bl)))"

lemma height_Leaf [simp]: "Leaf n \<longrightarrow> height n = 0"
  by (metis height.elims)

lemma Leaf_ind [simp]: "Leaf (Node n l) = Leaf (Node n (Empty#l))"
  by (metis Leaf.simps ListOfEmpty.simps list.distinct(1) list.sel(3) nattree.inject)

lemma not_ListOfEmpty_imp_not_Empty_existence [simp] :"\<not> ListOfEmpty l \<longrightarrow> (\<exists>x \<in> set l. x \<noteq> Empty)"
proof (induction l)
  case Nil
  then show ?case
    by (simp add: ListOfEmpty.Nil) 
next
  case (Cons a l)
  then have  "(\<forall>x \<in> set l. x = Empty) \<longrightarrow> ListOfEmpty l"
    by auto
  then have "a = Empty \<and> (\<forall>x \<in> set l. x = Empty) \<longrightarrow> ListOfEmpty (a#l)"
    using ListOfEmpty.Cons by blast 
  then have "\<not> ListOfEmpty (a#l) \<longrightarrow> (a \<noteq> Empty \<or> (\<exists>x \<in> set l. x \<noteq> Empty))"
    by blast
  then show ?case by simp
qed
  
lemma not_Leaf_imp_not_List_of_empty [simp]: 
"\<not> Leaf (Node n l) \<longrightarrow> (\<exists>x \<in> set l. x \<noteq> Empty)"    
proof -
  have "\<not> Leaf (Node n l) \<longrightarrow> \<not> ListOfEmpty l"
    using Leaf.intros by blast
  then show ?thesis using not_ListOfEmpty_imp_not_Empty_existence
    by blast 
qed
   
lemma Leaf_non_ListOfEmpty [simp]: 
"(\<exists>x \<in> set l. x \<noteq> Empty) = (\<not> Leaf (Node n l))"
proof -
  have "(\<exists>x \<in> set l. x \<noteq> Empty) \<longrightarrow> (\<not> Leaf (Node n l))"
    by (metis Leaf.cases increasing_tree_branch_list_of_empty increasing_tree_ind 
lt_nat_tree.elims(2) nat_less_le nattree.inject)
  then show ?thesis using not_Leaf_imp_not_List_of_empty by blast
qed
    
lemma height_ge [simp]: "\<forall>x \<in> set l. height x  \<le> height (Node n l)"
proof (induction l)
  case Nil
  then show ?case
    by (metis empty_iff empty_set) 
next
  case (Cons a l)
  have a1: "height (Node n (Cons a l)) = (if Leaf (Node n (Cons a l)) then 0 else Suc (ListMax 
(map height (Cons a l))))"
    using height.simps(2) by blast 
  then show ?case 
  proof (cases "a")
    case Empty
    then show ?thesis
      by (metis (no_types, lifting) Leaf_non_ListOfEmpty Listmax_ge a1 height.simps(1) image_eqI 
le_SucI list.set_map order_refl) 
  next
    case (Node x21 x22)
    then show ?thesis
      by (metis (no_types, lifting) Leaf_non_ListOfEmpty Listmax_ge a1 height.simps(1) image_eqI 
le_SucI le_numeral_extra(3) list.set_map) 
  qed
qed

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

text "I use Type nat option to screen out a branch without a labelled node; however I still use ListMax assuming there
is only one node labelled by the second argument."
inductive ListOfNone :: "('a option) list \<Rightarrow> bool" where 
  Nil: "ListOfNone []"
| Cons : "ListOfNone n \<Longrightarrow> ListOfNone (None#n)"

fun maxOption :: "nat option \<Rightarrow> nat option \<Rightarrow> nat option" where
  "maxOption None x = x"
| "maxOption (Some n) x = (case x of Some m \<Rightarrow> Some (max n m) | None \<Rightarrow> Some n)" 
  
definition ListMaxOption :: "(nat option) list \<Rightarrow> nat option" where
  "ListMaxOption l = foldr maxOption l None"

definition SucOption :: "nat option \<Rightarrow> nat option" where
  "SucOption n = (case n of None \<Rightarrow> None | Some n \<Rightarrow> Some (Suc n))"
  
fun le_option :: "nat option \<Rightarrow> nat option \<Rightarrow> bool" where  
  "le_option None _ = True"
| "le_option (Some n) x = (case x of None \<Rightarrow> False | Some m \<Rightarrow> n \<le> m)"

text "We don't care None cases"
fun lt_option :: "nat option \<Rightarrow> nat option \<Rightarrow> bool" where
 "lt_option (Some m) (Some n) = (m < n)"
  
fun depth :: "nattree \<Rightarrow> nat \<Rightarrow> nat option" where
  "depth Empty n = None"
| "depth (Node n bl) m = (if n = m 
                          then (Some 0) 
                          else SucOption (ListMaxOption (map (\<lambda>x. depth x m) bl)))"

definition H :: "bool list \<Rightarrow> nat set" where
  "H l = {x. x \<le> length l \<and> \<not> (nth (False#l) x)}"

definition isHonest :: "bool list \<Rightarrow> nat \<Rightarrow> bool" where
  "isHonest l x = (\<not> (nth (False#l) x))"
  
lemma H_0 [simp]: "0 \<in> H l"
  by (simp add: H_def)
  
lemma getFrom_suc_eq_H [simp]: "x < length l \<and> \<not> nth l x \<longleftrightarrow> Suc x \<in> H l"
  by (simp add: H_def less_eq_Suc_le)
  

fun ListSum :: "nat list \<Rightarrow> nat" where
  "ListSum l = foldr plus l 0"

lemma ListSum_0 [simp] :"(\<forall>x \<in> set l. x = 0) \<longrightarrow> ListSum l = 0" 
  proof (induction l)
    case Nil
    then show ?case by simp
  next
    case (Cons a l)
    then show ?case
      by simp 
  qed
text "No prunning used as we don't yet have an increasing tree in argument, but can improve it later"

fun count_node :: "nat \<Rightarrow> nattree \<Rightarrow> nat" where
  "count_node _ Empty = 0"
| "count_node m (Node n bl) = (of_bool (m = n)) + ListSum (map (count_node m) bl)"

lemma count_node_Leaf [simp] : "Leaf (Node n l) \<longrightarrow> count_node m (Node n l) = of_bool (m = n)"
proof -
  have "Leaf (Node n l) \<longrightarrow> (\<forall>x \<in> set l. count_node m x = 0)"
    by (metis Leaf_non_ListOfEmpty count_node.simps(1)) 
  then have "Leaf (Node n l) \<longrightarrow>  ListSum (map (count_node m) l) = 0"
    by (metis ListSum_0 Listmax_ge le_zero_eq listmax_0)    
  then show ?thesis
    using count_node.simps(2) by presburger 
qed
    
definition unique_node :: "nattree \<Rightarrow> nat \<Rightarrow> bool" where
  "unique_node t n = (count_node n t = 1)"

text "This function returns true only if each member in a set has one and only associated node."
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
  
lemma max_node_max [simp]: "\<forall> m. max_node t < m  \<longrightarrow> count_node m t = 0"
  proof (induction t)
    case Empty
    then show ?case
      by simp 
  next
    case (Node x1 x2)
    have a: "max_node (Node x1 x2) = ListMax (x1 # (map max_node x2))" 
      by simp
    then have "\<forall>x \<in> set x2. max_node x \<le> max_node (Node x1 x2) \<and> x1 \<le> max_node (Node x1 x2)"
      by simp
    then have "\<forall>x. \<forall>y \<in> set x2 . max_node (Node x1 x2)< x \<longrightarrow> max_node y < x \<and> x1 < x"
      using le_less_trans by blast  
    then have "\<forall>x. \<forall>y \<in> set x2 . max_node (Node x1 x2)< x \<longrightarrow> count_node x y = 0"
      by (simp add: Node.IH)
    then have "\<forall>x. max_node (Node x1 x2)< x \<longrightarrow> count_node x (Node x1 x2) =  ListSum (map (count_node x) x2)"
      by (smt Listmax_ge a add.commute add_cancel_left_right count_node.simps(2) list.set_intros(1) 
          not_le of_bool_def)
      then show ?case
      using ListSum_0 \<open>\<forall>x. \<forall>y\<in>set x2. max_node (Node x1 x2) < x \<longrightarrow> count_node x y = 0\<close> by auto 
  qed
  
fun increasing_depth_H :: "nattree \<Rightarrow> bool list \<Rightarrow> bool" where 
  "increasing_depth_H t l = (\<forall>x \<in> H l. \<forall>y \<in> H l. x < y \<longrightarrow>  lt_option (depth t x)  (depth t y))"

inductive root_label_0 :: "nattree \<Rightarrow> bool" where
  "root_label_0 (Node 0 l)"
  
lemma root_label_0_depth_0 [simp] : "root_label_0 n \<longrightarrow> depth n 0 = Some 0"
  by (metis depth.simps(2) root_label_0.cases)
  
text "F |- w" 
fun isFork :: "bool list \<Rightarrow> nattree \<Rightarrow> bool" where
  "isFork w F = ((length w \<ge> max_node F) 
               \<and> (increasing_tree F) 
               \<and> (uniqueH_tree F w) 
               \<and> (increasing_depth_H F w)
               \<and> root_label_0 F)"

lemma isFork_max_not_exceed [simp] : "isFork w F \<longrightarrow> length w \<ge> max_node F" by simp

lemma isFork_root_0 [simp] : "isFork w F \<longrightarrow> root_label_0 F" by simp

lemma isFork_increasing_tree [simp] : "isFork w F \<longrightarrow> increasing_tree F"
  using isFork.simps by blast 
    
lemma isFork_uniqueH_tree [simp] : "isFork w F \<longrightarrow> (\<forall>x \<in> H w. unique_node F x)"
  by (meson isFork.elims(2) uniqueH_tree_in_imp_l)

lemma isFork_increasing_depth_H [simp] : 
"isFork w F \<longrightarrow> (\<forall> x \<in> H w. \<forall> y \<in> H w. x < y \<longrightarrow> lt_option (depth F x) (depth F y))"
  by (meson increasing_depth_H.elims(2) isFork.elims(2))  
  
fun getLabelFromTine :: "nattree \<Rightarrow> nat list \<Rightarrow> nat list" where 
  "getLabelFromTine Empty l = []"
| "getLabelFromTine _ [] = []"
| "getLabelFromTine (Node _ l) (x#xs) = (if x \<ge> length l then [] else 
                                           (case nth l x of 
                                            Empty \<Rightarrow> [] | (*it runs out of nodes before we can trace down all paths*)
                                            Node n _ \<Rightarrow> n # getLabelFromTine (hd (drop x l)) xs))"  

text "This function provides a set of all path possible, starting from a root by comparing between
the length of lists of all choices of edges and lists of their labels."
fun set_of_tines :: "nattree \<Rightarrow> (nat list) set" where
  "set_of_tines t  = {tine. length tine = length (getLabelFromTine t tine)}"  

fun edge_disjoint_tines :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "edge_disjoint_tines [] _ = True" 
| "edge_disjoint_tines _ [] = True"
| "edge_disjoint_tines (x#xs) (y#ys) = (x\<noteq>y)"

text "Definition 4.11: flatTree"
fun flatTree :: "nattree \<Rightarrow> bool" where
 "flatTree F = 
(\<exists> t1 \<in> set_of_tines F. 
 \<exists> t2 \<in> set_of_tines F. 
 length t1 = length t2 
 \<and> length t1 = height F 
 \<and> edge_disjoint_tines t1 t1)"  

lemma Leaf_imp_nil_label_tine [simp]: assumes "Leaf (Node n l)" shows "getLabelFromTine (Node n l) t = []" 
  proof (cases t)
    case Nil
    then show ?thesis
      using getLabelFromTine.simps(2) by blast 
  next
    case (Cons a list)
    then show ?thesis 
      proof (cases "a \<ge> length l")
        case True
        then show ?thesis
          using getLabelFromTine.simps(3) local.Cons by presburger 
      next 
        case False 
        have "a < length l"
          using False by auto
        then have "nth l a = Empty"
          using Leaf_non_ListOfEmpty assms nth_mem by blast 
        then show ?thesis
          by (simp add: local.Cons)         
      qed
  qed
 
lemma flatTree_trivial [simp]: assumes "Leaf (Node n l)" shows "flatTree (Node n l)"
proof -
  have "set_of_tines (Node n l) = {tine. length tine = length (getLabelFromTine (Node n l) tine)}"
    by (metis set_of_tines.elims)
  then have "set_of_tines (Node n l) = {tine. length tine = length []}"
    by (metis (no_types, lifting) Collect_cong Leaf_imp_nil_label_tine assms list.size(3))
  then have "set_of_tines (Node n l) = {tine. length tine = 0}"
    by (metis (no_types) \<open>set_of_tines (Node n l) = {tine. length tine = length []}\<close> list.size(3))
  then have "set_of_tines (Node n l) = {[]}"
    by blast
  then show "flatTree (Node n l)"
    by (metis assms edge_disjoint_tines.simps(1) flatTree.simps height.simps(2) list.size(3) singletonI)
qed      

definition isForkable :: "bool list \<Rightarrow> bool" where
  "isForkable w = (\<exists>F. isFork w F \<and> flatTree F)"
  
definition flatFork :: "bool list \<Rightarrow> nattree \<Rightarrow> bool" where
  "flatFork w F = (isFork w F \<and> flatTree F)"

inductive ListOfAdverse :: "bool list \<Rightarrow> bool" where
  Nil : "ListOfAdverse []"  
| Cons : "ListOfAdverse xs \<Longrightarrow> ListOfAdverse (True#xs)"
  
lemma ListOfAdverse_all_True [simp]: "ListOfAdverse w \<longrightarrow> (\<forall> x \<in> set w. x)"
proof (induction w)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
    have "ListOfAdverse (a#w) \<longrightarrow> a"
      using ListOfAdverse.cases by blast
  then show ?case
    using Cons.IH ListOfAdverse.cases by auto 
qed
  
lemma all_True_ListOfAdverse [simp]: "(\<forall> x \<in> set w. x) \<longrightarrow> ListOfAdverse w"
proof (induction w)
  case Nil
  then show ?case
    by (simp add: ListOfAdverse.Nil) 
next
  case (Cons a w)
  then have "a = True \<and> (\<forall>x \<in> set w. x) \<longrightarrow> ListOfAdverse (a#w)"
    using ListOfAdverse.Cons by blast 
  then show ?case by simp
qed
  
lemma singleton_H_ListOfAdverse [simp]: "ListOfAdverse w \<longrightarrow> H w = {0}"
proof (induction w)
  case Nil
  then show ?case
    using H_def by auto 
next
  case (Cons a w)
    have "ListOfAdverse (a#w) \<longrightarrow> a"
      using ListOfAdverse.cases by blast
    then have "ListOfAdverse (a#w) \<longrightarrow> (\<forall> x. x \<le> length w \<longrightarrow> nth (False#(a#w)) x = nth (False#w) x)"
      by (smt ListOfAdverse_all_True add.right_neutral add_Suc_right insert_iff le_SucI list.simps(15) list.size(4) nth_equal_first_eq)
    have "ListOfAdverse (a#w) \<longrightarrow> (nth (False#(a#w)) (length (a#w)))"
      by (smt ListOfAdverse_all_True length_0_conv linear list.distinct(1) nth_equal_first_eq)
  then show ?case
    by (smt Collect_cong H_0 H_def ListOfAdverse_all_True mem_Collect_eq nth_equal_first_eq singleton_conv) 
qed
  
lemma ListOfEmpty_max_node_ListMax_0 [simp]: 
  assumes "ListOfEmpty l" 
  shows "ListMax (map max_node l) = 0"
  by (metis Leaf.simps Leaf_non_ListOfEmpty assms listmax_0 map_eq_map_tailrec max_node.simps(1))
  
lemma max_node_Leaf [simp]: 
  assumes "Leaf (Node n l)" 
  shows "max_node (Node n l) = n"    
proof -
  have "max_node (Node n l) = ListMax (n#(map max_node l))" by simp
  then have "max_node (Node n l) = max n (ListMax (map max_node l))"
    using ListMax_def by auto
  then show "max_node (Node n l) = n "
    using  Leaf.simps assms by auto
qed
    
lemma flatFork_Trivial : assumes "Leaf (Node 0 l)" and "ListOfAdverse w" shows "flatFork w (Node 0 l)"  
proof - 
  have "flatTree (Node 0 l)"
    using assms(1) flatTree_trivial by blast
  have prem1: "length w \<ge> max_node (Node 0 l)"
    using assms(1) max_node_Leaf by presburger
  have prem2: "increasing_tree (Node 0 l)"
    using Leaf.cases assms(1) increasing_tree_branch_list_of_empty by blast
  have "count_node 0 (Node 0 l) = 1"
    by (metis (full_types) assms(1) count_node_Leaf of_bool_eq(2))
  have "H w = {0}" using assms(2) singleton_H_ListOfAdverse by blast
  then have prem3: "uniqueH_tree (Node 0 l) w" 
    by (smt assms(1) count_node_Leaf of_bool_eq(2) singletonD uniqueH_tree_in_imp_r unique_node_def) 
  have prem4:"increasing_depth_H (Node 0 l) w"
    by (simp add: \<open>H w = {0}\<close>)
  have "root_label_0 (Node 0 l)"
    by (simp add: root_label_0.intros)  
  then show ?thesis
    using \<open>flatTree (Node 0 l)\<close> flatFork_def isFork.elims(3) prem1 prem2 prem3 prem4 by blast
qed
      
lemma forkable_eq_exist_flatfork [simp] : "isForkable w \<longleftrightarrow> (\<exists>F. flatFork w F)"
  using flatFork_def isForkable_def by blast
  
text "Definition 4.13 is really tricky as we have to traverse F and F' whether it holds that F \<subseteq> F' at 
the same time."
fun isPrefix_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "isPrefix_list [] _ = True"
| "isPrefix_list (l#ls) [] = False"
| "isPrefix_list (l#ls) (r#rs) = ((l=r) \<and> isPrefix_list ls rs)"
  
definition isPrefix_tine :: "nattree \<Rightarrow> nattree \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
 "isPrefix_tine nt1 nt2 t1 t2 = 
(isPrefix_list t1 t2 \<and> isPrefix_list (getLabelFromTine nt1 t1) (getLabelFromTine nt2 t2))"
 
definition isPrefix_tree :: "nattree \<Rightarrow> nattree \<Rightarrow> bool" where
  "isPrefix_tree nt1 nt2 =
    (\<forall>t1 \<in> set_of_tines nt1. \<forall>t2 \<in> set_of_tines nt2. isPrefix_list t1 t2 
    \<longrightarrow> isPrefix_tine nt1 nt2 t1 t2)"
  
text "as this can consider from any list of natural numbers."
definition isPrefix_fork :: "bool list \<Rightarrow> bool list \<Rightarrow> nattree \<Rightarrow> nattree \<Rightarrow> bool" where
  "isPrefix_fork w1 w2 nt1 nt2 = 
    (isFork w1 nt1 \<and> isFork w2 nt2 \<and> isPrefix_list w1 w2 \<and> isPrefix_tree nt1 nt2)"  
  
text "Definition 4.14"
fun closedFork_Hgiven :: "nattree \<Rightarrow> nat set \<Rightarrow> bool" where
  "closedFork_Hgiven Empty _ = True"
| "closedFork_Hgiven (Node n l) h = (if ListOfEmpty l 
                                     then (n \<in> h) 
                                     else foldr conj (map (\<lambda>x. closedFork_Hgiven x h) l) True)"

text "A closed fork has to be a fork of a certain string and closed in regard to that string."
definition closedFork :: "nattree \<Rightarrow> bool list \<Rightarrow> bool" where
  "closedFork F w = (isFork w F \<and> closedFork_Hgiven F (H w))"

lemma closedFork_ListOfAdverse [simp]: 
  assumes "Leaf (Node 0 l)" and "ListOfAdverse w" 
  shows "closedFork (Node 0 l) w"
proof -
  have "closedFork_Hgiven (Node 0 l) (H w)"
    by (metis H_0 Leaf.cases assms(1) closedFork_Hgiven.simps(2) nattree.inject) 
  then show ?thesis
    using assms(1) assms(2) closedFork_def flatFork_Trivial flatFork_def by blast 
qed

lemma not_ListOfAdverse_not_trivial_fork [simp]:
  assumes "Leaf (Node 0 l)" and "\<not> ListOfAdverse w"
  shows "\<not> isFork w (Node 0 l)"
proof -
  have "\<exists> x \<in> set w. \<not> x"
    using all_True_ListOfAdverse assms(2) by blast
  then have "\<exists> x. x > 0 \<and> x \<le> length w \<and> \<not> (nth (False#w) x)"
    by (metis Suc_leI in_set_conv_nth nth_Cons_Suc zero_less_Suc)
  then have "\<exists> x. x > 0 \<and> x \<in> H w"
    by (simp add: H_def) 
  then have "\<not> uniqueH_tree (Node 0 l) w"
    by (metis One_nat_def assms(1) max_node_Leaf max_node_max nat.simps(3) uniqueH_tree_in_imp_l unique_node_def) 
  then show ?thesis
    using isFork.simps by blast
qed    
    
lemma Leaf_inp_ListOfAdverse_trivial_fork [simp]:
  assumes "Leaf (Node 0 l)" 
  shows "ListOfAdverse w \<longleftrightarrow> isFork w (Node 0 l)"
  using assms flatFork_Trivial flatFork_def not_ListOfAdverse_not_trivial_fork by blast
    
text "From Definition 4.15, gap reserve and reach depend on a fork and a characteristic string."
text "A gap of a tine is a difference between its length and the longest tine's."
definition gap :: "nattree \<Rightarrow> nat list \<Rightarrow> nat" where
  "gap nt tine = height nt - length tine"
 
text "A reserve of a tine is the number of adversarial nodes after the last node of the tine."
definition reserve :: "bool list \<Rightarrow> nat list \<Rightarrow> nat" where
  "reserve w labeledTine = foldr (\<lambda>x.(plus (of_bool x)))  (drop (ListMax labeledTine) w) 0"

text "A reach of a tine is simply a difference between its reserve and gap."
definition reach :: "nattree \<Rightarrow> bool list \<Rightarrow> nat list \<Rightarrow> int" where
  "reach nt w tine = int (reserve w (getLabelFromTine nt tine)) - int (gap nt tine)"
  
text "lambda and mu (or called margin) from Definition 4.16."  
definition lambda :: "nattree \<Rightarrow> bool list \<Rightarrow> int" where
  "lambda t w = (GREATEST r. \<exists> x \<in> set_of_tines t. r = reach t w x)"

lemma lambda_no_honest : assumes "ListOfAdverse w" shows "\<exists>t. isFork w t \<and> lambda t w \<ge> 0"
proof -
  obtain l where "ListOfEmpty l"
    using ListOfEmpty.Nil by auto 
  obtain t where a:"Leaf t \<and> t = Node 0 l \<and> isFork w t"
    using Leaf.intros Leaf_inp_ListOfAdverse_trivial_fork \<open>ListOfEmpty l\<close> assms by blast
  have b:"gap t [] = 0"
    by (metis \<open>Leaf t \<and> t = Node 0 l \<and> isFork w t\<close> gap_def height_Leaf list.size(3) minus_nat.diff_0)
  have "reserve w [] \<ge> 0"
    by simp
  have reachge0: "reach t w [] \<ge> 0" 
    using \<open>gap t [] = 0\<close> reach_def by auto
  have nilin:"[] \<in> set_of_tines t"
by (metis (mono_tags, lifting) \<open>Leaf t \<and> t = Node 0 l \<and> isFork w t\<close> getLabelFromTine.simps(2) mem_Collect_eq set_of_tines.simps)
  then have c:"\<exists> x \<in> set_of_tines t. reach t w x \<ge> 0"
    using reachge0 by blast
  then have "\<exists>y. y = (GREATEST r. \<exists> x \<in> set_of_tines t. r = reach t w x)"
    by blast
  then have "(GREATEST r. \<exists> x \<in> set_of_tines t. r = reach t w x) \<ge> reach t w []" 
    using nilin a b c
  proof -
    have "\<And>ns. getLabelFromTine t ns = []"
      by (metis (lifting) Leaf_imp_nil_label_tine a)
    then have f1: "\<And>bs ns. reach t bs ns = int (reserve bs [])"
      using b gap_def reach_def by auto
  obtain ii :: "(int \<Rightarrow> bool) \<Rightarrow> int \<Rightarrow> int" where
    f2: "\<And>p i. (\<not> p i \<or> p (ii p i) \<or> Greatest p = i) \<and> (\<not> p i \<or> \<not> ii p i \<le> i \<or> Greatest p = i)"
    using Greatest_equality by moura
  have f3: "\<And>i. (\<forall>ns. ns \<notin> set_of_tines t \<or> i \<noteq> reach t w ns) \<or> int (reserve w []) = i"
    using f1 by presburger
  have f4: "\<exists>ns. ns \<in> set_of_tines t \<and> int (reserve w []) = reach t w ns"
    using f1 by (metis nilin)
  have "\<And>i. (\<forall>ns. ns \<notin> set_of_tines t \<or> i \<noteq> reach t w ns) \<or> (GREATEST i. \<exists>ns. ns \<in> set_of_tines t \<and> i = reach t w ns) = i \<or> ii (\<lambda>i. \<exists>ns. ns \<in> set_of_tines t \<and> i = reach t w ns) i = int (reserve w [])"
    using f2 f3
  proof -
    fix i :: int
    { fix nns :: "nat list"
      { assume "(\<exists>ns. ns \<in> set_of_tines t \<and> i = reach t w ns) \<and> (\<forall>ns. ns \<notin> set_of_tines t \<or> ii (\<lambda>i. \<exists>ns. ns \<in> set_of_tines t \<and> i = reach t w ns) i \<noteq> reach t w ns)"
        then have "(GREATEST i. \<exists>ns. ns \<in> set_of_tines t \<and> i = reach t w ns) = i"
          by (smt f2)
           (* > 1.0 s, timed out *)
        then have "nns \<notin> set_of_tines t \<or> (GREATEST i. \<exists>ns. ns \<in> set_of_tines t \<and> i = reach t w ns) = i \<or> reach t w nns \<noteq> i \<or> ii (\<lambda>i. \<exists>ns. ns \<in> set_of_tines t \<and> i = reach t w ns) i = int (reserve w [])"
          by meson }
      then have "nns \<notin> set_of_tines t \<or> (GREATEST i. \<exists>ns. ns \<in> set_of_tines t \<and> i = reach t w ns) = i \<or> reach t w nns \<noteq> i \<or> ii (\<lambda>i. \<exists>ns. ns \<in> set_of_tines t \<and> i = reach t w ns) i = int (reserve w [])"
        using c f1 by auto }
    then show "(\<forall>ns. ns \<notin> set_of_tines t \<or> i \<noteq> reach t w ns) \<or> (GREATEST i. \<exists>ns. ns \<in> set_of_tines t \<and> i = reach t w ns) = i \<or> ii (\<lambda>i. \<exists>ns. ns \<in> set_of_tines t \<and> i = reach t w ns) i = int (reserve w [])"
    by blast
qed
    then have "\<And>i. (\<forall>ns. ns \<notin> set_of_tines t \<or> i \<noteq> reach t w ns) \<or> (\<forall>ns. ns \<notin> set_of_tines t \<or> i \<noteq> reach t w ns) \<or> \<not> int (reserve w []) \<le> i \<or> (GREATEST i. \<exists>ns. ns \<in> set_of_tines t \<and> i = reach t w ns) = i"
      using f2
      by (metis (mono_tags, lifting))  (* > 1.0 s, timed out *)
    then have "(GREATEST i. \<exists>ns. ns \<in> set_of_tines t \<and> i = reach t w ns) = int (reserve w [])"
      using f4 by blast
    then show ?thesis
      using f1 by force
  qed
   then have "(GREATEST r. \<exists> x \<in> set_of_tines t. r = reach t w x) \<ge> 0"
     using reachge0 by linarith 
   then show ?thesis
     by (metis a lambda_def)
 qed
   
definition set_of_edge_disjoint_tines :: "nattree \<Rightarrow> ((nat list, nat list) prod) set" where
 "set_of_edge_disjoint_tines t
   = {(x,y). x \<in> set_of_tines t 
      \<and> y \<in> set_of_tines t
      \<and> edge_disjoint_tines x y}" 
    
definition margin :: "nattree \<Rightarrow>  bool list \<Rightarrow> int" where
  "margin t w = (GREATEST r. (\<exists> (a,b) \<in> set_of_edge_disjoint_tines t. r = min (reach t w a) (reach t w b)))"

lemma margin_no_honest : assumes "ListOfAdverse w" shows "\<exists>t. isFork w t \<and> margin t w \<ge> 0"
proof -
   obtain l where "ListOfEmpty l"
    using ListOfEmpty.Nil by auto 
  obtain t where a:"Leaf t \<and> t = Node 0 l \<and> isFork w t"
    using Leaf.intros Leaf_inp_ListOfAdverse_trivial_fork \<open>ListOfEmpty l\<close> assms by blast
  have b:"gap t [] = 0"
    by (metis \<open>Leaf t \<and> t = Node 0 l \<and> isFork w t\<close> gap_def height_Leaf list.size(3) minus_nat.diff_0)
  have "reserve w [] \<ge> 0"
    by simp
  have reachge0: "reach t w [] \<ge> 0" 
    using \<open>gap t [] = 0\<close> reach_def by auto
  have nilin:"[] \<in> set_of_tines t"
by (metis (mono_tags, lifting) \<open>Leaf t \<and> t = Node 0 l \<and> isFork w t\<close> getLabelFromTine.simps(2) mem_Collect_eq set_of_tines.simps)
  then have c:"\<exists> x \<in> set_of_tines t. reach t w x \<ge> 0"
    using reachge0 by blast
  then have d: "([],[]) \<in> set_of_edge_disjoint_tines t" 
    using nilin set_of_edge_disjoint_tines_def by auto
  then have e:"\<exists> (a,b) \<in> set_of_edge_disjoint_tines t. min (reach t w a) (reach t w b)\<ge>0"
    using reachge0 by auto
  then have f:"\<exists> y. y = (GREATEST r. (\<exists> (a,b) \<in> set_of_edge_disjoint_tines t. r = min (reach t w a) (reach t w b)))"
    by blast
  then have "(GREATEST r. (\<exists> (a,b) \<in> set_of_edge_disjoint_tines t. r = min (reach t w a) (reach t w b))) \<ge> reach t w []" 
    using a b c d e f  
  proof -
    have "\<And>ns. getLabelFromTine t ns = []"
      by (metis (lifting) Leaf_imp_nil_label_tine a)
    then have f1: "\<And>bs ns. reach t bs ns = int (reserve bs [])"
      using b gap_def reach_def by auto
  obtain ii :: "(int \<Rightarrow> bool) \<Rightarrow> int \<Rightarrow> int" where
    f2: "\<And>p i. (\<not> p i \<or> p (ii p i) \<or> Greatest p = i) \<and> (\<not> p i \<or> \<not> ii p i \<le> i \<or> Greatest p = i)"
    using Greatest_equality by moura
  have f3: "\<And>i. (\<forall>ns. ns \<notin> set_of_edge_disjoint_tines t \<or> i \<noteq> min (reach t w (fst ns)) (reach t w (snd ns))) \<or> int (reserve w []) = i"
    using f1 by presburger
  have f4: "\<exists>ns. ns \<in> set_of_edge_disjoint_tines t \<and> int (reserve w []) =  min (reach t w (fst ns)) (reach t w (snd ns))"
    using f1 d by auto 
  have "\<And>i. (\<forall>ns. ns \<notin> set_of_edge_disjoint_tines t \<or> i \<noteq> min (reach t w (fst ns)) (reach t w (snd ns))) 
\<or> (GREATEST i. \<exists>ns. ns \<in> set_of_edge_disjoint_tines t \<and> i = min (reach t w (fst ns)) (reach t w (snd ns))) = i 
\<or> ii (\<lambda>i. \<exists>ns. ns \<in> set_of_edge_disjoint_tines t \<and> i = min (reach t w (fst ns)) (reach t w (snd ns))) i = int (reserve w [])"
    by (simp add: Greatest_equality f1)
  then have "\<And>i.  (\<forall>ns. ns \<notin> set_of_edge_disjoint_tines t \<or> i \<noteq> min (reach t w (fst ns)) (reach t w (snd ns))) 
\<or> \<not> int (reserve w []) \<le> i \<or> (GREATEST i. \<exists>ns. ns \<in> set_of_edge_disjoint_tines t \<and> i = min (reach t w (fst ns)) (reach t w (snd ns))) = i"
      using f2
      by (metis (mono_tags, lifting))  (* > 1.0 s, timed out *)
    then have "(GREATEST i. \<exists>ns. ns \<in> set_of_edge_disjoint_tines t \<and> i = min (reach t w (fst ns)) (reach t w (snd ns))) = int (reserve w [])"
      using f4 by blast
    then show ?thesis
      using f1 by force
  qed
   then have "(GREATEST i. (\<exists> (a,b) \<in> set_of_edge_disjoint_tines t. i = min (reach t w a) (reach t w b))) \<ge> 0"
     using reachge0 by linarith
  then show ?thesis
    by (metis a margin_def) 
  qed
    
text "This function is to construct, from an increasing tree, a tree not containing greater-labelled 
nodes than a certain number."
  
fun remove_greater :: "nat \<Rightarrow> nattree \<Rightarrow> nattree" where
    "remove_greater _ Empty = Empty" (*Don't care*)
  | "remove_greater m (Node n l) = (if n < m then Node n (map (remove_greater m) l) else Empty)"

definition max_honest_node :: "bool list \<Rightarrow> nat" where
  "max_honest_node w = (GREATEST r. r \<in> H w)"
   
fun count_node_by_set :: "nat set \<Rightarrow> nattree \<Rightarrow> nat" where
  "count_node_by_set _ Empty = 0"
| "count_node_by_set s (Node n l) = (of_bool (n \<in> s)) +  ListSum (map (count_node_by_set s) l)"  

definition count_honest_node :: "bool list \<Rightarrow> nattree \<Rightarrow> nat" where
  "count_honest_node w t = count_node_by_set (H w) t"

lemma map_ListOfEmpty [simp]: "ListOfEmpty (map (\<lambda>x. Empty) l)"
  apply (induction l)
  apply (simp add: ListOfEmpty.Nil)
  by (simp add: ListOfEmpty.Cons)
  
(*This definition makes me reconsider the definition of prefixes of tines and forks.*)
fun toClosedFork :: "bool list \<Rightarrow> nattree \<Rightarrow> nattree" where
  "toClosedFork _ Empty = Empty"
| "toClosedFork w (Node n l) =
(if  count_honest_node w (Node n l) = of_bool (isHonest w n)
  then 
    (if isHonest w n then Node n (map (\<lambda>x. Empty) l) else Empty)
  else Node n (map (toClosedFork w) l)
)"

lemma isFork_toClosedFork_isFork [simp]: "isFork w F \<longrightarrow> isFork w (toClosedFork w F)"
  sorry
    
lemma closedFork_eq_toClosedFork [simp]: "isFork w F \<longrightarrow> F = (toClosedFork w F)"
  sorry 

lemma toClosedFork_prefixFork [simp]: "isFork w F \<longrightarrow> isPrefix_fork w w F (toClosedFork w F)"
  sorry
    
lemma closedFork_deepest_honest_node_eq_height [simp]: "isFork w F \<and> closedFork F w \<longrightarrow> 
          depth (ClosedFork w F) (max_honest_node w) = Some (height F)"
  sorry
    
lemma obtain_two_non_negative_reach_tines_toClosedFork [simp]: 
  assumes "isFork w F \<and> flatFork w F" 
  shows "t1 \<in> set (tinelist F) \<and> t2 \<in> set (tinelist F) 
\<and> length t1 = length t2 \<and> length t1 = height F 
\<longrightarrow> 
(\<exists> t1' \<in> set (tinelist (toClosedFork w F)). 
\<exists> t2' \<in> set (tinelist (toClosedFork w F)). 
isPrefix_tine (toClosedFork w F) F t1' t1 
\<and> isPrefix_tine (toClosedFork w F) F t2' t2
\<and> edge_disjoint_tines t1' t2' 
\<and> reach (toClosedFork w F) w t1' \<ge> 0 
\<and> reach (toClosedFork w F) w t2' \<ge> 0)"  
  sorry
  
lemma if_4_17 [simp]: assumes "isForkable w" shows  "(\<exists> F.(isFork w F \<and> margin F w \<ge> 0))"
proof -
  obtain F where a: "isFork w F \<and> flatTree F"
    using assms isForkable_def by blast
  then have "flatFork w F"
    using flatFork_def by blast 
  then obtain t1 and t2 where "t1 \<in> set_of_tines F \<and> t2 \<in> set_of_tines F 
\<and> length t1 = length t2 \<and> length t1 = height F"
    using flatTree.simps a by blast    
  obtain F' where "F' = toClosedFork w F"
    by simp
  then have lem1: "(\<exists> t1' \<in> set_of_tines F'. \<exists> t2' \<in> set_of_tines F'. 
isPrefix_tine F' F t1' t1 \<and> edge_disjoint_tines t1' t2' \<and> isPrefix_tine  F' F t2' t2 
\<and> reach F' w t1' \<ge> 0 \<and> reach F' w t2' \<ge> 0)" 
    using obtain_two_non_negative_reach_tines_toClosedFork
\<open>flatFork w F\<close> \<open>t1 \<in> set_of_tines F \<and> t2 \<in> set_of_tines F \<and> length t1 = length t2 
\<and> length t1 = height F\<close> a 
    sorry
  have "isFork w F'"
    using \<open>F' = toClosedFork w F\<close> a isFork_toClosedFork_isFork by blast
  then have "margin F' w \<ge> 0"
    sorry     
  then show ?thesis
    using a sorry 
qed
  
lemma only_if_4_17 [simp]: assumes  "(\<exists> F.(isFork w F \<and> margin F w \<ge> 0))" shows " isForkable w"
proof -
  obtain F where "isFork w F \<and> margin F w \<ge> 0"
    using assms by blast 
  show ?thesis sorry  
qed
  
proposition proposition_4_17 : "isForkable w \<longleftrightarrow> (\<exists> F.(isFork w F \<and> margin F w \<ge> 0))"
  using if_4_17 only_if_4_17 by blast 
 
definition lambda_of_string :: "bool list \<Rightarrow> int" where   
  "lambda_of_string w = (GREATEST t. (\<exists>F.(isFork w F \<and> closedFork F w \<and> t = lambda F w)))"

lemma isFork_Nil : "isFork [] F \<longrightarrow> Leaf F \<and> root_label_0 F"
  sorry
    
lemma lambda_of_nil : "lambda_of_string [] = 0"  
sorry

    
definition margin_of_string :: "bool list \<Rightarrow> int" where
  "margin_of_string w = (GREATEST t. (\<exists>F.(isFork w F \<and> closedFork F w \<and> t = margin F w)))"

definition m :: "bool list \<Rightarrow> (int, int) prod" where
  "m w = (lambda_of_string w, margin_of_string w)"
  
lemma lambda_nil : "lambda_of_string [] = 0"
  sorry
    
lemma lemma_4_18_trivial_case : "m [] = (0,0)"
sorry
  
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