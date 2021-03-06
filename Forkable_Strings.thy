theory Forkable_Strings imports Main "~~/src/HOL/List" "~~/src/HOL/Finite_Set" begin

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

lemma ListMax_member [simp]: "l = [] \<or> (\<exists> x \<in> set l. ListMax l = x)"   
  proof (induction l)
    case Nil
    then show ?case by simp
  next
    case (Cons a l)
    have "a#l \<noteq> []" by simp
    then show ?case 
    proof (cases "l = []")
      case True
      then have "ListMax (a#l) = max a (foldr max l 0)"
        by (metis ListMax_def foldr.simps(2) o_def)
      hence "ListMax (a#l) = a"
        by (metis ListMax_0 ListMax_def True max_0R)
      then show ?thesis
        by (metis list.set_intros(1)) 
    next
      case False
        then have "ListMax (a#l) = max a (foldr max l 0)"
        by (metis ListMax_def foldr.simps(2) o_def)
      hence "ListMax (a#l) = ListMax l \<or> ListMax (a#l) = a"
        by (metis ListMax_def max_def)
      then show ?thesis
        by (metis Cons.IH False insert_iff list.set(2)) 
    qed
      
  qed
 
fun height :: "nattree \<Rightarrow> nat" where
  "height Empty = 0"  
| "height (Node n bl) = (if Leaf (Node n bl) then 0 else Suc (ListMax (map height bl)))"

(*used in the proof of termination only*)
fun size_from_height :: "nattree \<Rightarrow> nat" where
  "size_from_height Empty = 0"
| "size_from_height (Node n l) = Suc (ListMax (map size_from_height l))"  
  
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
                                             
lemma ListMaxOption_none_imp_all_none [simp]: "ListMaxOption l = None \<longleftrightarrow> (\<forall>x \<in> set l. x = None)" 
proof (induction l)
  case Nil
    hence "ListMaxOption [] =  None"
      by (simp add: ListMaxOption_def)
  then show ?case
    by simp 
  next
    case (Cons y ys)
      hence "ListMaxOption (y#ys) = maxOption y (foldr maxOption ys None)"
        by (simp add: ListMaxOption_def)
      hence "ListMaxOption (y#ys) = None \<longrightarrow> y = None \<and> (foldr maxOption ys None) = None"
        by (metis (no_types, lifting) maxOption.elims option.case_eq_if option.simps(3))
    then show ?case
      using Cons.IH ListMaxOption_def by force 
  qed
                                   
definition SucOption :: "nat option \<Rightarrow> nat option" where
  "SucOption n = (case n of None \<Rightarrow> None | Some n \<Rightarrow> Some (Suc n))"

lemma SucOption_ne_Some_0 [simp]: "SucOption x \<noteq> Some 0"
  apply (cases x)
   apply (simp_all add: SucOption_def)
   done
  
lemma SucOption_none [simp]: "SucOption x = None \<longrightarrow> x = None"
  by (simp add: SucOption_def option.case_eq_if)  
  
text "We don't care None cases"
inductive lt_option :: "nat option \<Rightarrow> nat option \<Rightarrow> bool" where
"m < n \<Longrightarrow> lt_option (Some m) (Some n)"  
 
inductive le_option :: "nat option \<Rightarrow> nat option \<Rightarrow> bool" where
"m \<le> n \<Longrightarrow> le_option (Some m) (Some n)"

fun depth :: "nattree \<Rightarrow> nat \<Rightarrow> nat option" where
  "depth Empty n = None"
| "depth (Node n bl) m = (if n = m 
                          then (Some 0) 
                          else SucOption (ListMaxOption (map (\<lambda>x. depth x m) bl)))"
  
definition H :: "bool list \<Rightarrow> nat set" where
  "H l = {x. x \<le> length l \<and> \<not> (nth (False#l) x)}"

definition isHonest :: "bool list \<Rightarrow> nat \<Rightarrow> bool" where
  "isHonest l x = (x \<in> H l)"
  
lemma H_0 [simp]: "0 \<in> H l"
  by (simp add: H_def)
  
lemma getFrom_suc_eq_H [simp]: "x < length l \<and> \<not> nth l x \<longleftrightarrow> Suc x \<in> H l"
  by (simp add: H_def less_eq_Suc_le)
  

fun ListSum :: "nat list \<Rightarrow> nat" where
  "ListSum l = foldr plus l 0"

lemma ListSum_0 [simp] :"(\<forall>x \<in> set l. x = 0) \<longleftrightarrow> ListSum l = 0" 
  proof (induction l)
    case Nil
    then show ?case by simp
  next
    case (Cons a l)
    then show ?case
      by simp 
  qed
    
lemma ListSum_ge [simp] : "\<forall>x \<in> set l. ListSum l \<ge> x"
  proof (induction l)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
      hence "ListSum (x#xs) = x + ListSum xs"
        by simp
      hence "ListSum (x#xs) \<ge> x" by simp
    then show ?case using Cons.IH by auto
  qed
    
lemma ListSum_ge_lifting_2 [simp] : "(x \<in> set l \<and> y \<in> set l \<and> x \<noteq> y \<longrightarrow> ListSum (map f l) \<ge> (f x) + (f y))"
proof (induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case 
    proof (cases l)
      case Nil
      then show ?thesis
        by auto 
    next
      case (Cons ht tl)
      hence "a = x \<longrightarrow> (x \<in> set (a#ht#tl) \<and> y \<in> set (a#ht#tl) \<and> x \<noteq> y \<longrightarrow> y \<noteq> a)"
        by auto
      hence "a = x \<longrightarrow> (x \<in> set (a#ht#tl) \<and> y \<in> set (a#ht#tl) \<and> x \<noteq> y \<longrightarrow> y \<in> set (ht#tl))"
        by auto
      hence "a = x \<longrightarrow> (x \<in> set (a#ht#tl) \<and> y \<in> set (a#ht#tl) \<and> x \<noteq> y \<longrightarrow> ListSum (map f (ht#tl)) \<ge> (f y)) "
        by (metis ListSum_ge image_eqI set_map)
      hence ax:"a = x \<longrightarrow> (x \<in> set (a#ht#tl) \<and> y \<in> set (a#ht#tl) \<and> x \<noteq> y \<longrightarrow> ListSum (map f (a#ht#tl)) \<ge> f x + (f y)) "
        by auto
      have "a = y \<longrightarrow> (x \<in> set (a#ht#tl) \<and> y \<in> set (a#ht#tl) \<and> x \<noteq> y \<longrightarrow> x \<noteq> a)"
        by auto
      hence "a = y \<longrightarrow> (x \<in> set (a#ht#tl) \<and> y \<in> set (a#ht#tl) \<and> x \<noteq> y \<longrightarrow> x \<in> set (ht#tl))"
        by auto
      hence "a = y \<longrightarrow> (x \<in> set (a#ht#tl) \<and> y \<in> set (a#ht#tl) \<and> x \<noteq> y \<longrightarrow> ListSum (map f (ht#tl)) \<ge> (f x)) "
        by (metis ListSum_ge image_eqI set_map)
      hence ay:"a = y \<longrightarrow> (x \<in> set (a#ht#tl) \<and> y \<in> set (a#ht#tl) \<and> x \<noteq> y \<longrightarrow> ListSum (map f (a#ht#tl)) \<ge> f y + (f x)) "
        by auto    
      have "a \<noteq> y \<and> a \<noteq> x \<longrightarrow> (x \<in> set (a#ht#tl) \<and> y \<in> set (a#ht#tl) \<and> x \<noteq> y \<longrightarrow> ListSum (map f (ht#tl)) \<ge> f y + (f x))"
        using Cons.IH local.Cons by auto
      then show ?thesis using ax ay
        by (smt ListSum.simps add.commute foldr.simps(2) le_add2 list.simps(9) local.Cons o_apply order.trans)
    qed
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
    
lemma unique_node_branches [simp]: assumes "unique_node (Node n l) m" and "\<exists> x \<in> set l. count_node m x = 1" 
  shows "x \<in> set l \<and> y \<in> set l \<and> count_node m x = 1 \<and> count_node m y = 1 \<longrightarrow> x = y"  
proof (rule ccontr)
  assume 1:"\<not> (x \<in> set l \<and> y \<in> set l \<and> count_node m x = 1 \<and> count_node m y = 1 \<longrightarrow> x = y)"
  hence "x \<in> set l \<and> y \<in> set l \<and> count_node m x = 1 \<and> count_node m y = 1 \<and> x \<noteq> y"
    by auto  
  hence "count_node m (Node n l) = (of_bool (m = n)) + ListSum (map (count_node m) l)"
    by simp
  hence "count_node m (Node n l) \<ge> 2"
    by (metis ListSum_ge_lifting_2 \<open>x \<in> set l \<and> y \<in> set l \<and> count_node m x = 1 \<and> count_node m y = 1 \<and> x \<noteq> y\<close> nat_1_add_1 trans_le_add2)
  thus "False"
    using assms(1) unique_node_def by auto
qed

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
        by (metis (full_types) ListSum_0 Listmax_ge \<open>\<forall>x. \<forall>y\<in>set x2. max_node (Node x1 x2) < x \<longrightarrow> count_node x y = 0\<close> le_zero_eq listmax_0)
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
    
function getLabelFromTine :: "nattree \<Rightarrow> nat list \<Rightarrow> nat list" where 
  "getLabelFromTine Empty l = []"
| "getLabelFromTine _ [] = []"
| "getLabelFromTine (Node _ l) (x#xs) = (if x \<ge> length l then [] else 
                                           (case nth l x of 
                                            Empty \<Rightarrow> [] | (*it runs out of nodes before we can trace down all paths*)
                                            Node n _ \<Rightarrow> n # getLabelFromTine (nth l x) xs))"
  apply (metis list.exhaust max_node.cases old.prod.exhaust)
  apply simp
  apply blast
  apply simp
  apply blast
  apply blast
  by auto 

termination getLabelFromTine
apply (relation "measure (\<lambda>(i,N). length N)")
apply simp
by (metis case_prod_conv impossible_Cons in_measure not_less)    
  
definition set_of_tines :: "nattree \<Rightarrow> (nat list) set" where
  "set_of_tines t  = {tine. length tine = length (getLabelFromTine t tine)}"    
text "This function provides a set of all path possible, starting from a root by comparing between
the length of lists of all choices of edges and lists of their labels."
  
lemma getLabelFromTine_Leaf_nil : assumes "Leaf F" shows "getLabelFromTine F t = []"
proof -
  obtain l and n where "ListOfEmpty l \<and> F = Node n l"
    using Leaf.cases assms by blast
  thus ?thesis 
   proof (cases t)
     case Nil
     then show ?thesis
       by (simp add: \<open>ListOfEmpty l \<and> F = Node n l\<close>) 
   next
     case (Cons x xs)
     then show ?thesis 
       proof (cases "x \<ge> length l")
         case True
         then show ?thesis
           by (simp add: \<open>ListOfEmpty l \<and> F = Node n l\<close> local.Cons) 
       next
         case False
         then show ?thesis
           by (metis Leaf_non_ListOfEmpty \<open>ListOfEmpty l \<and> F = Node n l\<close> assms eq_iff 
getLabelFromTine.simps(3) less_imp_le_nat linorder_neqE_nat local.Cons nattree.simps(4) nth_mem)
       qed
   qed
 qed
   
lemma getLabelFromTine_shorter_eq_height [simp]: "length (getLabelFromTine F t) \<le> height F"
proof (induction t arbitrary:F)
     case Nil
     then show ?case
       by (metis getLabelFromTine.simps(2) less_eq_nat.simps(1) list.size(3))
   next
     case (Cons x xs)
     then show ?case 
       proof (induction F)
         case Empty
         then show ?case by simp
       next
         case (Node n l)
           have "getLabelFromTine (Node n l) (x#xs) = (if x \<ge> length l then [] else 
                                           (case nth l x of 
                                            Empty \<Rightarrow> [] | (*it runs out of nodes before we can trace down all paths*)
                                            Node m _ \<Rightarrow> m # getLabelFromTine (nth l x) xs))" using getLabelFromTine.simps(3) by simp
           then show ?case 
             proof (cases "x \<ge> length l")
               case True
               then show ?thesis
                 by (metis getLabelFromTine.simps(3) le0 list.size(3)) 
             next
               case False
               then show ?thesis 
                 proof (cases "nth l x")
                   case Empty
                   then show ?thesis
                     by (metis \<open>getLabelFromTine (Node n l) (x # xs) = (if length l \<le> x then [] else 
case l ! x of Empty \<Rightarrow> [] | Node m xa \<Rightarrow> m # getLabelFromTine (l ! x) xs)\<close> le0 list.size(3) nattree.simps(4)) 
                 next
                   case (Node m bl)
                     hence "getLabelFromTine (Node n l) (x#xs) = m # getLabelFromTine (nth l x) xs"
                       using False
                       by (simp add: Node)  
                     hence "length (getLabelFromTine (Node n l) (x#xs)) = Suc (length (getLabelFromTine (nth l x) xs))"
                       by simp
                     hence "length (getLabelFromTine (nth l x) xs) \<le> height (nth l x)"
                       by (simp add: Node.prems)
                     hence  "length (getLabelFromTine (Node n l) (x#xs)) \<le> Suc (height (nth l x))"
                       using \<open>length (getLabelFromTine (Node n l) (x # xs)) = Suc (length (getLabelFromTine (l ! x) xs))\<close> by linarith
                     have "Suc (height (nth l x)) \<le> height (Node n l)"
                       by (metis (no_types, lifting) False Listmax_ge \<open>getLabelFromTine (Node n l) (x # xs) = m # getLabelFromTine (l ! x) xs\<close> getLabelFromTine_Leaf_nil height.simps(2) image_eqI linorder_not_le list.distinct(1) not_less_eq_eq nth_mem set_map)
                     then show ?thesis
                       using \<open>length (getLabelFromTine (Node n l) (x # xs)) \<le> Suc (height (l ! x))\<close> le_trans by blast 
                 qed
             qed
       qed
 qed
        
lemma getLabelFromTine_shorter_eq_tine [simp]: "length (getLabelFromTine F t) \<le> length t"
  sorry
    
lemma set_of_tines_Empty [simp]: "set_of_tines Empty = {[]}"
proof -
  have "set_of_tines Empty  = {tine. length tine = length (getLabelFromTine Empty tine)}"
    by (simp add: set_of_tines_def)
  thus ?thesis by auto
qed
   
lemma getLabelFromTine_branch_notin [simp]: "x \<ge> length l \<longrightarrow> x#xs \<notin> set_of_tines (Node n l)"
proof -
  have 1: "x \<ge> length l \<longrightarrow> getLabelFromTine (Node n l) (x#xs)= []"
    by simp
  hence "length (x#xs) \<noteq> length []"
    by simp
  hence 2:"x \<ge> length l \<longrightarrow> length (x#xs) \<noteq> length (getLabelFromTine (Node n l) (x#xs))" using 1 by simp
  have "\<forall> tine \<in> set_of_tines (Node n l). length tine = length (getLabelFromTine (Node n l) tine)"
    by (simp add: set_of_tines_def)
  thus ?thesis
    by auto 
qed
  
lemma getLabelFromTine_branch_in_if [simp]: 
  assumes "x < length l \<and> xs \<in> set_of_tines (nth l x) \<and> (nth l x \<noteq> Empty)" shows "x#xs \<in> set_of_tines (Node n l)"
proof (cases "nth l x")
  case Empty
  then show ?thesis
    using assms
    by blast 
next
  case (Node m bl)
  have "getLabelFromTine (Node n l) (x#xs) = m # getLabelFromTine (nth l x) xs"
    using Node assms
    by (metis getLabelFromTine.simps(3) leD nattree.simps(5)) 
  hence "length (getLabelFromTine (nth l x) xs) = length xs"
    using assms
      by (simp add: \<open>x < length l \<and> xs \<in> set_of_tines (l ! x) \<and> l ! x \<noteq> Empty\<close> set_of_tines_def) 
    then show ?thesis
      using \<open>getLabelFromTine (Node n l) (x # xs) = m # getLabelFromTine (l ! x) xs\<close> set_of_tines_def by auto  
qed

lemma getLabelFromTine_branch_in_onlyif [simp]: assumes "x#xs \<in> set_of_tines (Node n l)" shows "x < length l \<and> xs \<in> set_of_tines (nth l x) \<and> (nth l x \<noteq> Empty)"  
proof -
  have "length (x#xs) = length (getLabelFromTine (Node n l) (x#xs))"
    using assms
    by (simp add: set_of_tines_def) 
  have len:"x < length l"
  proof -
    have "\<not> length l \<le> x"
      by (metis assms getLabelFromTine_branch_notin)
    then show ?thesis
      by auto
  qed
  have empty:"nth l x \<noteq> Empty"
    by (metis \<open>length (x # xs) = length (getLabelFromTine (Node n l) (x # xs))\<close> assms 
getLabelFromTine.simps(3) getLabelFromTine_branch_notin length_0_conv list.simps(3) nattree.simps(4))
  then obtain m bl where "nth l x = Node m bl" using len
    using max_node.cases by blast
  hence "getLabelFromTine (Node n l) (x#xs) = m # getLabelFromTine (nth l x) xs" using len empty
    by (metis getLabelFromTine.simps(3) leD nattree.simps(5))
  thus ?thesis
    using \<open>length (x # xs) = length (getLabelFromTine (Node n l) (x # xs))\<close> len
    by (simp add: empty set_of_tines_def)
qed

lemma getLabelFromTine_branch_in [simp]: "x#xs \<in> set_of_tines (Node n l) \<longleftrightarrow> x < length l \<and> xs \<in> set_of_tines (nth l x) \<and> (nth l x \<noteq> Empty)"
  using getLabelFromTine_branch_in_if getLabelFromTine_branch_in_onlyif by blast
  
lemma nil_in_set_of_tines [simp]: "[] \<in> set_of_tines F"
  by (simp add: set_of_tines_def)  

lemma nth_in_fst [simp] : assumes "n < length x" shows "nth x n = nth (x@y) n"
  by (simp add: assms nth_append)

lemma finite_set_of_tines_aux_0_aux [simp]: "getLabelFromTine (Node n (xs@[Empty])) t = getLabelFromTine (Node n xs) t"
proof (cases t)
  case Nil
  then show ?thesis by simp
next
  case (Cons y ys)
  then show ?thesis 
    proof (cases "y \<ge> length (xs@[Empty])")
      case True
      hence L:"getLabelFromTine (Node n (xs@[Empty])) (y#ys) = []"
        by simp
      have R:"getLabelFromTine (Node n xs) (y#ys) = []" using True  by simp
      then show ?thesis using L
        by (simp add: local.Cons)  
    next
      case False
        hence lt1:"y < length (xs@[Empty])"
          by simp
      then show ?thesis 
        proof (cases "y = length xs")
          case True
          then show ?thesis
            by (simp add: local.Cons) 
        next
          case False
          hence  lt2:"y < length xs"
            by (metis length_append_singleton linorder_neqE_nat lt1 not_less_eq)
            hence nth_eq:"nth xs y = nth (xs@[Empty]) y"
              using nth_in_fst by blast
            hence L: "getLabelFromTine (Node n (xs@[Empty])) (y#ys) = (if y \<ge> length (xs@[Empty]) then [] else 
                                           (case nth (xs@[Empty]) y of 
                                            Empty \<Rightarrow> [] |
                                            Node m _ \<Rightarrow> m # getLabelFromTine (nth (xs@[Empty]) y) ys))"
              using getLabelFromTine.simps(3) by blast   
            hence  L: "getLabelFromTine (Node n (xs@[Empty])) (y#ys) =  (case nth (xs@[Empty]) y of 
                                            Empty \<Rightarrow> [] | 
                                            Node m _ \<Rightarrow> m # getLabelFromTine (nth (xs@[Empty]) y) ys)"
              using lt1 by auto
            have R:"getLabelFromTine (Node n xs) (y#ys) =  
                                            (case nth xs y of 
                                            Empty \<Rightarrow> [] | 
                                            Node m _ \<Rightarrow> m # getLabelFromTine (nth xs y) ys)"
              using getLabelFromTine.simps(3) lt2 by presburger 
          then show ?thesis using L R nth_eq
            using local.Cons by presburger
        qed
    qed
qed
  
lemma finite_set_of_tines_aux_0 [simp]: "set_of_tines (Node n (xs@[Empty])) = set_of_tines (Node n xs)"
proof -
  have "set_of_tines (Node n (xs@[Empty])) = {tine. length tine = length (getLabelFromTine (Node n (xs@[Empty])) tine)}"
    using set_of_tines_def by auto
  hence "set_of_tines (Node n (xs@[Empty])) = {tine. length tine = length (getLabelFromTine (Node n xs) tine)}"
    by auto
  thus ?thesis
    by (simp add: set_of_tines_def)
qed   

lemma finite_set_of_tines_aux_1_aux [simp]: "length y = length (getLabelFromTine (Node n (xs@[Node m l])) y) 
       \<longrightarrow> y \<in> set_of_tines (Node n xs) \<or> y \<in> {r. \<exists>s \<in> set_of_tines (Node m l). r = (length xs)#s}"
proof (cases y)
  case Nil
  then show ?thesis
    by simp 
next
  case (Cons y ys)
    have "\<forall>y ys. y < length xs \<longrightarrow> getLabelFromTine (Node n (xs@[Node m l])) (y#ys) = (case nth (xs@[Node m l]) y of 
                                                                                          Empty \<Rightarrow> [] | 
                                                                                          Node p _ \<Rightarrow> p # getLabelFromTine (nth (xs@[Node m l]) y) ys)"
      by (metis Suc_leD getLabelFromTine.simps(3) length_append_singleton not_less) 
        
  hence 1:"\<forall>y ys. y < length xs \<longrightarrow> getLabelFromTine (Node n (xs@[Node m l])) (y#ys) = (case nth xs y of 
                                                                                          Empty \<Rightarrow> [] | 
                                                                                          Node p _ \<Rightarrow> p # getLabelFromTine (nth xs y) ys)"
    by (metis nth_in_fst)
   hence 2:"\<forall>y ys. y < length xs \<longrightarrow> getLabelFromTine (Node n xs) (y#ys) = (case nth xs y of 
                                                                                          Empty \<Rightarrow> [] | 
                                                                                          Node p _ \<Rightarrow> p # getLabelFromTine (nth xs y) ys)"
     using getLabelFromTine.simps(3) by presburger
   hence 3: "\<forall>y ys. y < length xs \<longrightarrow> getLabelFromTine (Node n xs) (y#ys) = getLabelFromTine (Node n (xs@[Node m l])) (y#ys)"
     using "1" by presburger
   have cons:"\<forall>y ys. length (y#ys) = length (getLabelFromTine (Node n (xs@[Node m l])) (y#ys)) 
       \<longrightarrow> (y#ys) \<in> set_of_tines (Node n xs) \<or> (y#ys) \<in> {r. \<exists>s \<in> set_of_tines (Node m l). r = (length xs)#s}"
     by (smt "3" Suc_le_eq getLabelFromTine.simps(3) length_Cons length_append_singleton length_greater_0_conv 
linorder_neqE_nat list.simps(3) mem_Collect_eq nat.inject nattree.simps(5) neq_if_length_neq nth_append_length 
set_of_tines_def)
  then show ?thesis
    using local.Cons by blast 
qed
  
lemma finite_set_of_tines_aux_1 [simp]: "set_of_tines (Node n (xs@[Node m l])) = set_of_tines (Node n xs) \<union> {r. \<exists>s \<in> set_of_tines (Node m l). r = (length xs)#s}"
proof -
  have "\<forall>y ys. y < length xs \<longrightarrow> getLabelFromTine (Node n (xs@[Node m l])) (y#ys) = (case nth (xs@[Node m l]) y of 
                                                                                          Empty \<Rightarrow> [] | 
                                                                                          Node p _ \<Rightarrow> p # getLabelFromTine (nth (xs@[Node m l]) y) ys)"
    by (metis Suc_leD getLabelFromTine.simps(3) length_append_singleton not_less) 
  hence 1:"\<forall>y ys. y < length xs \<longrightarrow> getLabelFromTine (Node n (xs@[Node m l])) (y#ys) = (case nth xs y of 
                                                                                          Empty \<Rightarrow> [] | 
                                                                                          Node p _ \<Rightarrow> p # getLabelFromTine (nth xs y) ys)"
    by (metis nth_in_fst)
   hence "\<forall>y ys. y < length xs \<longrightarrow> getLabelFromTine (Node n xs) (y#ys) = (case nth xs y of 
                                                                                          Empty \<Rightarrow> [] | 
                                                                                          Node p _ \<Rightarrow> p # getLabelFromTine (nth xs y) ys)"
     using getLabelFromTine.simps(3) by presburger
   hence lt:"\<forall>y ys. y < length xs \<longrightarrow> getLabelFromTine (Node n xs) (y#ys) = getLabelFromTine (Node n (xs@[Node m l])) (y#ys)"
     using "1" by presburger
  have "\<forall>x \<in> set_of_tines (Node n (xs@[Node m l])). x \<in> set_of_tines (Node n xs) \<union> {r. \<exists>s \<in> set_of_tines (Node m l). r = (length xs)#s}"
    using finite_set_of_tines_aux_1_aux
    by (simp add: set_of_tines_def) 
  hence "set_of_tines (Node n (xs@[Node m l])) \<subseteq> set_of_tines (Node n xs) \<union> {r. \<exists>s \<in> set_of_tines (Node m l). r = (length xs)#s}"
    by blast 
  have cons:"\<forall>y ys. length (y#ys) = length (getLabelFromTine (Node n xs) (y#ys)) 
       \<longrightarrow> (y#ys) \<in> set_of_tines (Node n (xs@[Node m l]))"
    using lt
    by (simp add: set_of_tines_def) 
  hence "\<forall>x. length x = length (getLabelFromTine (Node n xs) x) \<longrightarrow> x \<in> set_of_tines (Node n (xs@[Node m l]))"
    by (metis list.exhaust nil_in_set_of_tines) 
  hence main: "\<forall>x \<in> set_of_tines (Node n xs). x \<in> set_of_tines (Node n (xs@[Node m l]))"
    using set_of_tines_def by auto
  have "\<forall>x \<in> {r. \<exists>s \<in> set_of_tines (Node m l). r = (length xs)#s}. x \<in> set_of_tines (Node n (xs@[Node m l]))"
    by auto
  hence "set_of_tines (Node n xs) \<union> {r. \<exists>s \<in> set_of_tines (Node m l). r = (length xs)#s} \<subseteq> set_of_tines (Node n (xs@[Node m l]))" using main
    by blast
    then show ?thesis
      using \<open>set_of_tines (Node n (xs @ [Node m l])) \<subseteq> set_of_tines (Node n xs) \<union> {r. \<exists>s\<in>set_of_tines (Node m l). r = length xs # s}\<close> by blast   
qed

lemma finite_cons [simp]: assumes "finite x" shows "finite {r. \<exists>s \<in> x. r = m # s}"  
proof -
  have "{r. \<exists>s \<in> x. r = m # s} = (\<lambda>s. m#s)`x"
    by (simp add: image_def)
  thus ?thesis
    by (simp add: assms)
qed
  
lemma finite_set_of_tines [simp]: "finite (set_of_tines t)"
  proof (induction t)
    case Empty
    then show ?case
      by auto 
  next
    case (Node n l)
    then show ?case 
      proof (induct l rule: rev_induct)
        case Nil
          hence "set_of_tines (Node n []) = {tine. length tine = length (getLabelFromTine (Node n []) tine)}"
            by (simp add: set_of_tines_def)
          hence "set_of_tines (Node n []) = {tine. length tine = 0}"
            by (metis (no_types, lifting) Collect_cong Leaf.intros ListOfEmpty.Nil getLabelFromTine_Leaf_nil list.size(3))
          hence "set_of_tines (Node n []) = {[]}"
            by auto
          then show ?case
            by simp 
      next
        case (snoc x xs)
        then have "finite (set_of_tines x) \<and> ((\<forall>y \<in> set xs. finite (set_of_tines y)) \<longrightarrow> finite (set_of_tines (Node n xs)))"
          by (meson in_set_conv_decomp) 
        hence "(\<forall>y \<in> set xs. finite (set_of_tines y)) \<longrightarrow> finite (set_of_tines (Node n (xs@[x])))"
          proof (cases x)
            case Empty
            then show ?thesis 
              using snoc.hyps snoc.prems
              by (metis finite_set_of_tines_aux_0) 
          next
            case (Node m l)
            hence "finite (set_of_tines (Node m l))"
              using \<open>finite (set_of_tines x) \<and> ((\<forall>y\<in>set xs. finite (set_of_tines y)) \<longrightarrow> finite (set_of_tines (Node n xs)))\<close> 
              by blast
            hence "finite {r. \<exists>s\<in>set_of_tines (Node m l). r = length xs # s}"
              by simp 
            then show ?thesis
              using Node finite_set_of_tines_aux_1 snoc.hyps
              by (metis (no_types, lifting) finite_UnI) 
          qed
        then show ?case
          using finite_set_of_tines_aux_1 finite_set_of_tines_aux_0 snoc.prems
          by (metis UnCI set_append) 
      qed
  qed
  
fun edge_disjoint_tines :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "edge_disjoint_tines [] _ = True" 
| "edge_disjoint_tines _ [] = True"
| "edge_disjoint_tines (x#xs) (y#ys) = (x\<noteq>y)"

text "Definition 4.11: flatTree"
definition flatTree :: "nattree \<Rightarrow> bool" where
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
          using False
          by (simp add: not_le_imp_less) 
        then have "nth l a = Empty"
          using Leaf_non_ListOfEmpty assms nth_mem by blast 
        then show ?thesis
          using assms getLabelFromTine_Leaf_nil by blast      
      qed
  qed
 
lemma flatTree_trivial [simp]: assumes "Leaf (Node n l)" shows "flatTree (Node n l)"
proof -
  have "set_of_tines (Node n l) = {tine. length tine = length (getLabelFromTine (Node n l) tine)}"
    using set_of_tines_def by blast  
  then have "set_of_tines (Node n l) = {tine. length tine = length []}"
    by (metis (no_types, lifting) Collect_cong Leaf_imp_nil_label_tine assms list.size(3))
  then have "set_of_tines (Node n l) = {tine. length tine = 0}"
    by (metis (no_types) \<open>set_of_tines (Node n l) = {tine. length tine = length []}\<close> list.size(3))
  then have "set_of_tines (Node n l) = {[]}"
    by blast
  then show "flatTree (Node n l)"
    by (metis assms edge_disjoint_tines.simps(1) flatTree_def height.simps(2) list.size(3) nil_in_set_of_tines)
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
    using  Leaf.simps assms
    by (metis ListOfEmpty_max_node_ListMax_0 max_0R nattree.inject) 
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

lemma foldr_conj_eq_forall [simp]: "foldr conj l True \<longleftrightarrow> (\<forall> x \<in> set l. x)"    
  proof (induction l)
    case Nil
    then show ?case
      by auto 
  next
    case (Cons x xs)
    hence "foldr conj (x#xs) True = (x \<and> foldr conj xs True)"
      by auto
    then show ?case
      using Cons.IH by auto 
  qed
  
lemma closedFork_Hgiven_imp_branches [simp]: "closedFork_Hgiven (Node n l) h \<longrightarrow> (\<forall>z \<in> set l. closedFork_Hgiven z h)"
  proof (cases "ListOfEmpty l")
    case True
    then show ?thesis
      by (metis Leaf.intros Leaf_non_ListOfEmpty closedFork_Hgiven.simps(1)) 
  next
    case False
      hence "closedFork_Hgiven (Node n l) h \<longrightarrow> foldr conj (map (\<lambda>x. closedFork_Hgiven x h) l) True"
        by simp
       hence "closedFork_Hgiven (Node n l) h \<longrightarrow> (\<forall> x \<in> set (map (\<lambda>x. closedFork_Hgiven x h) l). x)"
         using foldr_conj_eq_forall by blast
       hence "closedFork_Hgiven (Node n l) h \<longrightarrow> (\<forall>x \<in> set l. closedFork_Hgiven x h \<in> set (map (\<lambda>x. closedFork_Hgiven x h) l)) "
         by simp   
    then show ?thesis  using \<open>closedFork_Hgiven (Node n l) h \<longrightarrow> (\<forall>x\<in>set (map (\<lambda>x. closedFork_Hgiven x h) l). x)\<close> by auto
  qed
  
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
  "lambda t w = Max {r. \<exists> x \<in> set_of_tines t. r = reach t w x}"

lemma ListOfAdverse_count_eq_length : 
  "ListOfAdverse w \<longrightarrow> (foldr (\<lambda>x.(plus (of_bool x))) w 0) = length w"
proof (induction w)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
    have "ListOfAdverse (Cons a w) \<longrightarrow> a \<and> ListOfAdverse w"
      using ListOfAdverse.cases by blast
    then have "ListOfAdverse (Cons a w) \<longrightarrow> a \<and> (foldr (\<lambda>x.(plus (of_bool x))) w 0) = length w"
      using Cons.IH  by blast
    then have "ListOfAdverse (Cons a w) \<longrightarrow> foldr (\<lambda>x.(plus (of_bool x))) (a # w) 0 = (\<lambda>x.(plus (of_bool x))) a (length w) "
      by (metis foldr_Cons o_apply) 
  then show ?case
    by (metis (full_types) One_nat_def \<open>ListOfAdverse (a # w) \<longrightarrow> a \<and> ListOfAdverse w\<close> list.size(4) of_bool_eq(2) semiring_normalization_rules(24)) 
qed
    
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
  have "\<forall> tine. getLabelFromTine t tine = []"
    using Leaf_imp_nil_label_tine a by blast 
  then have "\<forall> tine. length (getLabelFromTine t tine) = 0"
    by simp
  then have "set_of_tines t = {[]}"
    using set_of_tines_def
    by auto
  then have exist: "\<exists> x \<in> set_of_tines t. reach t w x \<ge> 0"
    using reachge0 by blast
  then have all: "\<forall> x \<in> set_of_tines t. reach t w x \<ge> 0"
    using \<open>set_of_tines t = {[]}\<close> by fastforce
  then have "{r. \<exists> x \<in> set_of_tines t. r = reach t w x} = {r. r = reach t w []}"
    using \<open>set_of_tines t = {[]}\<close> by auto
  hence "{r. \<exists> x \<in> set_of_tines t. r = reach t w x} = {r. r = int (reserve w (getLabelFromTine t [])) - int (gap t [])}"
    using reach_def by auto
  hence "{r. \<exists> x \<in> set_of_tines t. r = reach t w x} = {r. r = int (reserve w []) - 0}"
    by (metis b getLabelFromTine.simps(2) of_nat_0)
  hence "{r. \<exists> x \<in> set_of_tines t. r = reach t w x} = {r. r = int (foldr (\<lambda>x.(plus (of_bool x))) w 0)}"
    using reserve_def by auto
  hence "{r. \<exists> x \<in> set_of_tines t. r = reach t w x} = {int (length w)}"
    by (simp add: ListOfAdverse_count_eq_length assms)
  hence "lambda t w \<ge> 0"
    using lambda_def by auto
  thus ?thesis
    using a by blast 
 qed
   
definition set_of_edge_disjoint_tines :: "nattree \<Rightarrow> ((nat list, nat list) prod) set" where
 "set_of_edge_disjoint_tines t         
   = {(x,y). x \<in> set_of_tines t 
      \<and> y \<in> set_of_tines t
      \<and> edge_disjoint_tines x y}" 

lemma set_of_edge_disjoint_tines_finite : "finite (set_of_edge_disjoint_tines F)"
proof -
  have f1:"set_of_edge_disjoint_tines F = {(x,y). x \<in> set_of_tines F  \<and> y \<in> set_of_tines F \<and> edge_disjoint_tines x y}"
    by (simp add: set_of_edge_disjoint_tines_def) 
  have f2:"finite (set_of_tines F)"
    using finite_set_of_tines by auto
  hence "finite ((set_of_tines F) \<times> (set_of_tines F))"
    by auto
  hence "\<forall>a. fst a \<in> set_of_tines F  \<and> snd a \<in> set_of_tines F \<and> edge_disjoint_tines (fst a) (snd a) \<longrightarrow>  fst a \<in> set_of_tines F  \<and> (snd a) \<in> set_of_tines F"
    by simp
  hence "{(x,y). x \<in> set_of_tines F  \<and> y \<in> set_of_tines F \<and> edge_disjoint_tines x y} \<subseteq> {(x,y). x \<in> set_of_tines F  \<and> y \<in> set_of_tines F}"
    by blast 
  have "set_of_tines F \<times> set_of_tines F =  {(x,y). x \<in> set_of_tines F  \<and> y \<in> set_of_tines F}"
    by blast
  hence "finite {(x,y). x \<in> set_of_tines F  \<and> y \<in> set_of_tines F}"
    using \<open>finite (set_of_tines F \<times> set_of_tines F)\<close> by auto
  thus ?thesis
    using \<open>{(x, y). x \<in> set_of_tines F \<and> y \<in> set_of_tines F \<and> edge_disjoint_tines x y} \<subseteq> {(x, y). x \<in> set_of_tines F \<and> y \<in> set_of_tines F}\<close> f1 infinite_super
    by fastforce 
  qed
    
definition margin :: "nattree \<Rightarrow>  bool list \<Rightarrow> int" where
  "margin t w = Max {r. (\<exists> (a,b) \<in> set_of_edge_disjoint_tines t. r = min (reach t w a) (reach t w b))}"

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
   have "\<forall> tine. getLabelFromTine t tine = []"
    using Leaf_imp_nil_label_tine a by blast 
  then have "\<forall> tine. length (getLabelFromTine t tine) = 0"
    by simp
  then have set_nil:"set_of_tines t = {[]}"
    by (simp add: set_of_tines_def)
   then have c:"\<exists> x \<in> set_of_tines t. reach t w x \<ge> 0"
    using reachge0 by blast
  then have d: "set_of_edge_disjoint_tines t  
 = {(x,y). x \<in> {[]}
      \<and> y \<in> {[]}
      \<and> edge_disjoint_tines x y}"
    using set_nil set_of_edge_disjoint_tines_def by auto
  then have "\<forall> (a,b) \<in> set_of_edge_disjoint_tines t. 
 a = [] \<and> b= []"
    by simp
  then have "([],[]) \<in> set_of_edge_disjoint_tines t"
    by (simp add: case_prodI d)
  then have "set_of_edge_disjoint_tines t = {([],[])}"
    using \<open>\<forall>(a, b)\<in>set_of_edge_disjoint_tines t. a = [] \<and> b = []\<close> by blast
  then have "\<exists> (a,b) \<in> set_of_edge_disjoint_tines t. 
min (reach t w a) (reach t w b) \<ge> 0"
    by (simp add: reachge0)
  then have "\<forall> (a,b) \<in> set_of_edge_disjoint_tines t. 
min (reach t w a) (reach t w b) \<ge> 0"
    using \<open>set_of_edge_disjoint_tines t = {([], [])}\<close> by auto
  then have "{r. \<exists> (a,b) \<in> set_of_edge_disjoint_tines t. r = min (reach t w a) (reach t w b)} = {r. r = reach t w []}"
    using \<open>set_of_edge_disjoint_tines t = {([], [])}\<close> by auto
  hence "{r. \<exists> (a,b) \<in> set_of_edge_disjoint_tines t. r = min (reach t w a) (reach t w b)} = {r. r = int (reserve w (getLabelFromTine t [])) - int (gap t [])}"
    using reach_def by auto
  hence "{r. \<exists> (a,b) \<in> set_of_edge_disjoint_tines t. r = min (reach t w a) (reach t w b)} = {r. r = int (reserve w []) - 0}"
    by (metis b getLabelFromTine.simps(2) of_nat_0)
  hence "{r. \<exists> (a,b) \<in> set_of_edge_disjoint_tines t. r = min (reach t w a) (reach t w b)} = {r. r = int (foldr (\<lambda>x.(plus (of_bool x))) w 0)}"
    using reserve_def by auto
  hence "{r. \<exists> (a,b) \<in> set_of_edge_disjoint_tines t. r = min (reach t w a) (reach t w b)} = {int (length w)}"
    by (simp add: ListOfAdverse_count_eq_length assms)
  hence "margin t w \<ge> 0"
    using margin_def by auto
  thus ?thesis
    using a by blast 
 qed

text "This function is to construct, from an increasing tree, a tree not containing greater-labelled 
nodes than a certain number."

definition max_honest_node :: "bool list \<Rightarrow> nat" where
  "max_honest_node w = Max (H w)"
   
lemma finite_honest_node [simp]: "finite (H w)"
  proof (induct w rule: rev_induct)
    case Nil
    then show ?case
      by simp 
  next
    case (snoc w ws)
    have ws:"H ws = {x. x \<le> length ws \<and> \<not> (nth (False#ws) x)}"
      by (simp add: H_def)
    have ws_w : "H (ws@[w]) = {x. x \<le> length (ws@[w]) \<and> \<not> (nth (False#(ws@[w])) x)}"
      by (simp add: H_def) 
    hence imp:"\<forall>x. x \<le> length ws \<longrightarrow> (nth (False#ws) x =  nth (False#(ws@[w])) x)"
      by (metis (full_types) Cons_eq_appendI le_imp_less_Suc length_Cons nth_in_fst)
    hence "H (ws@[w]) = (if w then H ws else insert (length (ws@[w])) (H ws))"
    proof (cases w)
      case True
        hence "nth (False#(ws@[w])) (length (ws@[w]))"
          by simp
      then show ?thesis using ws ws_w
        by (smt Collect_cong Cons_eq_appendI True eq_iff le_imp_less_Suc length_Cons length_append_singleton nat_less_le not_less_eq_eq nth_in_fst)
      next
        case False
        hence "\<not> nth (False#(ws@[w])) (length (ws@[w]))"
          by simp
         hence "length (ws@[w]) \<in> H (ws@[w])"
           by (metis (no_types, lifting) eq_iff mem_Collect_eq ws_w)
         hence "H (ws@[w]) = {x. x= length (ws@[w]) \<or> (x \<le> length ws \<and> \<not> (nth (False#(ws@[w])) x))}" using ws_w
           by (smt Collect_cong False Suc_leD antisym dual_order.trans length_append_singleton mem_Collect_eq not_less_eq_eq)
         hence "H (ws@[w]) = {x. x= length (ws@[w]) \<or> x \<in> {x. x \<le> length ws \<and> \<not> (nth (False#ws) x)}}"
           by (smt Collect_cong imp mem_Collect_eq)
         then show ?thesis
           by (metis False insert_compr ws) 
    qed
    then show ?case
      by (metis finite_insert snoc.hyps) 
  qed 
  
lemma max_honest_node_le_length [simp]: "max_honest_node w \<le> length w"
proof -
  have "0 \<in> H w"
    using H_0 by blast
  have "\<forall>x \<in> H w. x \<le> length w"
    by (simp add: H_def)
  then show ?thesis using finite_honest_node
    by (metis Max_in \<open>0 \<in> H w\<close> equals0D max_honest_node_def) 
qed
 
fun count_node_by_set :: "nat set \<Rightarrow> nattree \<Rightarrow> nat" where
  "count_node_by_set _ Empty = 0"
| "count_node_by_set s (Node n l) = (of_bool (n \<in> s)) +  ListSum (map (count_node_by_set s) l)"     

definition count_honest_node :: "bool list \<Rightarrow> nattree \<Rightarrow> nat" where
  "count_honest_node w t = count_node_by_set (H w) t"
  
lemma map_ListOfEmpty [simp]: "ListOfEmpty (map (\<lambda>x. Empty) l)"
  apply (induction l)
  apply (simp add: ListOfEmpty.Nil)
  by (simp add: ListOfEmpty.Cons)  
  
function toClosedFork :: "bool list \<Rightarrow> nattree \<Rightarrow> nattree" where
  "toClosedFork _ Empty = Empty"
| "toClosedFork w (Node n l) = 
(if count_honest_node w (Node n l) = of_bool (isHonest w n) (*0 or 1 *)
  then 
    (if isHonest w n 
    then Node n (map (\<lambda>x. Empty) l)
    else  Empty)
  else Node n (map (toClosedFork w) l))"
  apply (metis isFork.cases size_from_height.cases)   
    apply simp
   apply blast
  by blast

termination toClosedFork 
apply (relation "measure (\<lambda>(i,N). size_from_height N)")
   apply simp
  by (simp add: le_imp_less_Suc)
    
lemma isFork_toClosedFork_isFork_aux_1 [simp]: 
 "length w \<ge> max_node F \<longrightarrow> length w \<ge> max_node (toClosedFork w F)"
proof (induction F)
  case Empty
  then show ?case by simp
next
  case (Node n l)    
    have "n \<le> max_node (Node n l)"
      by simp
  then show ?case 
    proof (cases "count_honest_node w (Node n l) = of_bool (isHonest w n)")
      case True
      then have "count_honest_node w (Node n l) = of_bool (isHonest w n)" by simp
      then show ?thesis 
        proof (cases "isHonest w n")
          case True (*solve this ambiguity*)
          then show ?thesis
            by (metis Leaf.intros \<open>count_honest_node w (Node n l) = of_bool (isHonest w n)\<close> 
\<open>n \<le> max_node (Node n l)\<close> dual_order.trans map_ListOfEmpty max_node_Leaf toClosedFork.simps(2)) 
        next 
          case False
          then have "toClosedFork w (Node n l) = Empty"
            by (metis True toClosedFork.simps(2))
          then show ?thesis
            by (metis le_0_eq linear max_node.simps(1))
      qed 
     next
      case False
        then have "toClosedFork w (Node n l) = Node n (map (toClosedFork w) l)"
          by simp
        hence "max_node (toClosedFork w (Node n l)) 
=  ListMax (n # (map max_node (map (toClosedFork w) l)))"
          using max_node.simps(2) by presburger     
        have f1 :"length w \<ge> max_node (Node n l) \<longrightarrow> length w \<ge> n"
          by (metis \<open>n \<le> max_node (Node n l)\<close> le_trans)
        have "length w \<ge> max_node (Node n l) \<longrightarrow> (\<forall> x \<in> set l. length w \<ge> max_node x)"
          by (metis Listmax_ge dual_order.trans image_eqI insertCI list.set(2) max_node.simps(2) set_map)  
        hence "length w \<ge> max_node (Node n l) \<longrightarrow> (\<forall> x \<in> set l. length w \<ge> max_node (toClosedFork w x))"
          by (metis Node.IH)            
        hence "l = [] \<or> (\<exists>x \<in> set (map max_node (map (toClosedFork w) l)). x = ListMax (map max_node (map (toClosedFork w) l)))"
          using ListMax_member 
          by (metis length_0_conv length_map) 
        hence "l = [] \<or> (\<exists>x \<in> set (map (toClosedFork w) l). max_node x = ListMax (map max_node (map (toClosedFork w) l)))"
          by (metis imageE set_map)
        hence "l = [] \<or> (\<exists>x \<in> set l. max_node (toClosedFork w x) = ListMax (map max_node (map (toClosedFork w) l)))"
          by (metis imageE set_map)
        then show ?thesis
          by (metis ListMax_member Listmax_ge 
\<open>max_node (Node n l) \<le> length w \<longrightarrow> (\<forall>x\<in>set l. max_node (toClosedFork w x) \<le> length w)\<close> 
\<open>max_node (toClosedFork w (Node n l)) = ListMax (n # map max_node (map (toClosedFork w) l))\<close> 
\<open>toClosedFork w (Node n l) = Node n (map (toClosedFork w) l)\<close> dual_order.trans f1 list.discI list.simps(8) set_ConsD)             
    qed    
  qed

lemma isFork_toClosedFork_isFork_aux_2 [simp]: 
"increasing_tree F \<longrightarrow> increasing_tree (toClosedFork w F)"
proof (induction F)
  case Empty
  then show ?case
    by simp 
next
  case (Node n l)
  then show ?case 
      proof (cases "count_honest_node w (Node n l) = of_bool (isHonest w n)")
        case True
        then have "count_honest_node w (Node n l) = of_bool (isHonest w n)" by simp
        then show ?thesis 
          proof (cases "isHonest w n")
            case True
            then show ?thesis
              by (metis \<open>count_honest_node w (Node n l) = of_bool (isHonest w n)\<close> 
                 increasing_tree_branch_list_of_empty map_ListOfEmpty toClosedFork.simps(2)) 
          next
            case False
            then show ?thesis
              using True increasing_tree.simps(1) toClosedFork.simps(2) by presburger 
          qed
      next
        case False
        then have "toClosedFork w (Node n l) = Node n (map (toClosedFork w) l)"
          by simp
        have " (\<And>x2a. x2a \<in> set l \<Longrightarrow> increasing_tree x2a \<longrightarrow> increasing_tree (toClosedFork w x2a))"
          using Node.IH by blast
        have "increasing_tree (Node n l) \<longrightarrow> (\<forall>x \<in> set l. increasing_tree x \<and> lt_nat_tree n x)"
          using increasing_tree_ind by blast 
        then have "\<forall>x \<in> set l. lt_nat_tree n x \<longrightarrow> lt_nat_tree n (toClosedFork w x)"
          by (metis (no_types, lifting) lt_nat_tree.simps(1) lt_nat_tree.simps(2) toClosedFork.elims) 
        then show ?thesis
          by (metis (mono_tags, lifting) Node.IH \<open>toClosedFork w (Node n l) = Node n (map (toClosedFork w) l)\<close> 
imageE image_set increasing_tree_ind) 
      qed
qed

lemma map_eq_map2 : "(\<forall> x \<in> set l. f x = f (g x)) \<longrightarrow> map f l = map f (map g l)"
  by simp

lemma honest_node_0_imp_0_each_honest_node : "count_honest_node w F = 0 \<longrightarrow> (\<forall> x \<in> H w. count_node x F = 0)"    
  proof (induction F)
    case Empty
    then show ?case
      using count_node.simps(1) by blast 
  next
    case (Node n l)
    then show ?case
      proof (cases "n \<in> H w")
        case True
          then have "count_honest_node w (Node n l) = (of_bool (n \<in> H w)) +  ListSum (map (count_node_by_set (H w)) l)"
            using count_honest_node_def count_node_by_set.simps(2) by presburger
          hence "count_honest_node w (Node n l) > 0"
            by (metis True add_is_0 gr_zeroI of_bool_eq(1) of_bool_eq_iff)
        then show ?thesis
          by linarith 
      next
        case False
          then have "count_honest_node w (Node n l) =  ListSum (map (count_node_by_set (H w)) l)"
            by (metis (mono_tags, lifting) add.left_neutral count_honest_node_def count_node_by_set.simps(2) of_bool_eq(1))
          hence "count_honest_node w (Node n l) = ListSum (map (count_honest_node w) l)"
            by (metis count_honest_node_def map_eq_conv)
          hence "count_honest_node w (Node n l) = 0 \<longrightarrow> (\<forall>x \<in> set l. count_honest_node w x = 0)"
            by (metis (full_types) ListSum_0 image_eqI set_map)
          hence "count_honest_node w (Node n l) = 0 \<longrightarrow> (\<forall>x \<in> set l. (\<forall>y \<in> H w. count_node y x = 0))"
            using Node.IH by blast
          then show ?thesis
            by (smt False \<open>count_honest_node w (Node n l) = 0 \<longrightarrow> (\<forall>x\<in>set l. count_honest_node w x = 0)\<close> 
\<open>count_honest_node w (Node n l) = ListSum (map (count_honest_node w) l)\<close> add_cancel_left_left count_node.elims map_eq_conv nattree.inject of_bool_eq(1))
      qed
  qed  
  
lemma isFork_toClosedFork_isFork_aux_3_aux [simp] :
  assumes "isHonest w n" shows "count_node n F = count_node n (toClosedFork w F)" 
proof (induction F)
  case Empty
  then show ?case
    using toClosedFork.simps(1) by presburger 
next
  case (Node m l)
  then show ?case
    proof (cases "count_honest_node w (Node m l) = of_bool (isHonest w m)")
      case True
        then have "count_honest_node w (Node m l) = of_bool (isHonest w m)"
          by simp
        then show ?thesis 
          proof (cases "isHonest w m")
            case True
            hence "isHonest w m"
              by simp 
            have "count_honest_node w (Node m l) = 1"
              by (simp add: True \<open>count_honest_node w (Node m l) = of_bool (isHonest w m)\<close>) 
            hence "count_honest_node w (toClosedFork w (Node m l)) =1"
              by (smt Leaf.intros Leaf_non_ListOfEmpty ListSum_0 Listmax_ge One_nat_def Suc_eq_plus1_left 
True count_honest_node_def count_node_by_set.simps(1) count_node_by_set.simps(2) isHonest_def le_0_eq 
listmax_0 map_ListOfEmpty of_bool_eq(2) toClosedFork.simps(2))
            hence ListSumhonest0 :"ListSum (map (count_honest_node w) l) = 0" 
              by (smt One_nat_def Suc_eq_plus1_left True \<open>count_honest_node w (Node m l) = 1\<close> add_diff_cancel_left' count_honest_node_def count_node_by_set.simps(2) isHonest_def map_eq_conv of_bool_eq(2))
            hence "\<forall>x \<in> set (map (count_honest_node w) l). x = 0"
              using ListSum_0 by blast
            hence "\<forall>x \<in> set l. count_honest_node w x = 0"
              by simp
            hence "\<forall>x \<in> set l. count_node n x = 0"
              using assms honest_node_0_imp_0_each_honest_node isHonest_def by blast
            hence "ListSum (map (count_node n) l) = 0"
              by (metis ListSumhonest0 \<open>\<forall>x\<in>set l. count_honest_node w x = 0\<close> list.map_cong0 map_eq_map_tailrec)
            hence "count_node n (Node m l) = of_bool (n = m)"
              by (metis Leaf.intros ListMax_0 ListOfEmpty.simps ListSum_0 Listmax_ge Suc_le_eq \<open>ListSum (map (count_node n) l) = 0\<close> count_node.simps(2) count_node_Leaf gr0_conv_Suc gr_implies_not0 list.map_disc_iff not_gr0)
            have "ListSum (map (count_honest_node w) (map (\<lambda>x. Empty) l)) = 0"
              by (smt ListSum_0 count_honest_node_def count_node_by_set.simps(1) imageE set_map)
            hence "count_node n (Node m (map (\<lambda>x. Empty) l)) = of_bool (n = m)"
              using Leaf.simps count_node_Leaf map_ListOfEmpty by blast
            then show ?thesis
              using True \<open>count_honest_node w (Node m l) = of_bool (isHonest w m)\<close> \<open>count_node n (Node m l) = of_bool (n = m)\<close> by auto    
          next
            case False
              hence "count_honest_node w (Node m l) = 0"
                by (simp add: True)
              hence "count_node n (Node m l) = 0"
                using assms honest_node_0_imp_0_each_honest_node isHonest_def by blast 
            then show ?thesis
              by (simp add: False \<open>count_honest_node w (Node m l) = 0\<close>) 
          qed
    next
      case False
        have "toClosedFork w (Node m l) = Node m (map (toClosedFork w) l)"
          by (simp add: False)
        hence LHS:"count_node n (Node m l) = (of_bool (m = n)) + ListSum (map (count_node n) l)"
        proof -
          show ?thesis
            by auto
        qed
        hence RHS:"count_node n (toClosedFork w (Node m l)) = (of_bool (m = n)) + ListSum (map (count_node n) (map (toClosedFork w) l))"
          using \<open>toClosedFork w (Node m l) = Node m (map (toClosedFork w) l)\<close>
        proof -
          have "count_node n (toClosedFork w (Node m l)) = of_bool (n = m) + ListSum (map (count_node n) (map (toClosedFork w) l))"
            using \<open>toClosedFork w (Node m l) = Node m (map (toClosedFork w) l)\<close> count_node.simps(2) by presburger
          then show ?thesis
            by auto
        qed
        have "\<forall>x \<in> set l. count_node n x = count_node n (toClosedFork w x)"
          by (simp add: Node.IH)
        hence "map (count_node n) l = map (count_node n) (map (toClosedFork w) l)"
          using map_eq_map2 by blast
      then show ?thesis using Node.IH LHS RHS by presburger
    qed
qed
  
lemma isFork_toClosedFork_isFork_aux_3 [simp]:
  "uniqueH_tree F w \<longrightarrow> uniqueH_tree (toClosedFork w F) w"
proof -
  have "\<forall> x \<in> H w. count_node x F = count_node x (toClosedFork w F)"
    using isFork_toClosedFork_isFork_aux_3_aux isHonest_def by blast
  hence "uniqueH_tree F w \<longrightarrow> (\<forall>x \<in> H w. unique_node F x)"
    using uniqueH_tree_def unique_nodes_by_nat_set.elims(2) by blast 
  hence "uniqueH_tree F w \<longrightarrow> (\<forall>x \<in> H w. unique_node (toClosedFork w F) x)"
    by (metis \<open>\<forall>x\<in>H w. count_node x F = count_node x (toClosedFork w F)\<close> unique_node_def)
  thus ?thesis
    using uniqueH_tree_in_imp_r by blast
qed
  
lemma none_depth_imp_zero_exist [simp]: "depth F m = None \<longrightarrow> count_node m F = 0"
proof (induction F)
  case Empty
  then show ?case
    by simp 
next
  case (Node n l) 
  hence depth:"depth (Node n l) m = (if n = m then (Some 0) else SucOption (ListMaxOption (map (\<lambda>x. depth x m) l)))"
    using depth.simps(2) by blast 
  hence "n = m \<longrightarrow> depth (Node n l) m = Some 0" by simp
  have "depth (Node n l) m = None \<longrightarrow> n \<noteq> m" using depth
    by fastforce 
  hence "depth (Node n l) m = None \<longrightarrow> SucOption (ListMaxOption (map (\<lambda>x. depth x m) l)) = None"
    by (metis depth)
  hence "depth (Node n l) m = None \<longrightarrow> ListMaxOption (map (\<lambda>x. depth x m) l) = None"
    using SucOption_none by blast
  hence "depth (Node n l) m = None \<longrightarrow> (\<forall>x \<in> set l. depth x m = None)" by (metis ListMaxOption_none_imp_all_none image_eqI image_set) 
  then show ?case
  proof -
    have f1: "\<forall>b. if b then of_bool b = (1::nat) else of_bool b = (0::nat)"
      by (meson of_bool_def)
    obtain nn :: "nat list \<Rightarrow> nat" where
      f2: "\<forall>ns. (nn ns \<in> set ns \<and> nn ns \<noteq> 0 \<or> ListSum ns = 0) \<and> ((\<forall>n. n \<notin> set ns \<or> n = 0) \<or> ListSum ns \<noteq> 0)"
      by (metis (no_types) ListSum_0)
    obtain nna :: "nattree set \<Rightarrow> (nattree \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nattree" where
      "\<forall>x0 x1 x2. (\<exists>v3. x2 = x1 v3 \<and> v3 \<in> x0) = (x2 = x1 (nna x0 x1 x2) \<and> nna x0 x1 x2 \<in> x0)"
      by moura
    then have "\<forall>n f N. n \<notin> f ` N \<or> n = f (nna N f n) \<and> nna N f n \<in> N"
      by (meson imageE)
    moreover
    { assume "nn (map (count_node m) l) \<notin> set (map (count_node m) l) \<or> nn (map (count_node m) l) = 0"
      then have "ListSum (map (count_node m) l) = 0"
        using f2 by metis
      then have "of_bool (n = m) = (0::nat) \<longrightarrow> of_bool (m = n) = (0::nat) \<and> ListSum (map (count_node m) l) = 0"
        by simp
      then have "depth (Node n l) m = None \<longrightarrow> depth (Node n l) m = None \<longrightarrow> count_node m (Node n l) = 0"
        using f1 \<open>depth (Node n l) m = None \<longrightarrow> n \<noteq> m\<close> count_node.simps(2) by presburger }
    ultimately show ?thesis
      by (metis (no_types) Node.IH \<open>depth (Node n l) m = None \<longrightarrow> (\<forall>x\<in>set l. depth x m = None)\<close> set_map)
  qed
qed

lemma zero_exist_imp_none_depth [simp]: "count_node m F = 0 \<longrightarrow> depth F m = None" 
proof (induction F)
  case Empty
  then show ?case
    by simp 
next
  case (Node n l)
    have "count_node m (Node n l) = 0 \<longrightarrow> n \<noteq> m \<and> ListSum (map (count_node m) l) = 0"
      by simp
    hence "count_node m (Node n l) = 0 \<longrightarrow> n \<noteq> m \<and> (\<forall>x \<in> set (map (count_node m) l). x = 0)"
      using ListSum_0 by blast
    hence "count_node m (Node n l) = 0 \<longrightarrow> n \<noteq> m \<and> (\<forall>x \<in> set l. count_node m x = 0)"
      by (metis image_eqI set_map)
    hence "count_node m (Node n l) = 0 \<longrightarrow> n \<noteq> m \<and> (\<forall>x \<in> set l. depth x m = None)"
      using Node.IH by blast  
  then show ?case
    by (metis (no_types, lifting) ListMaxOption_none_imp_all_none SucOption_def depth.simps(2) imageE image_set option.case_eq_if) 
qed
  
lemma isFork_toClosedFork_isFork_aux_4_aux [simp] : 
  "isHonest w m \<longrightarrow> depth F m = depth (toClosedFork w F) m"
proof (induction F)
  case Empty
  then show ?case
    by simp 
next
  case (Node n l)
  then show ?case 
  proof (cases "count_honest_node w (Node n l) = of_bool (isHonest w n)")
    case True
      hence "count_honest_node w (Node n l) = of_bool (isHonest w n)" by simp
      then show ?thesis 
      proof (cases "isHonest w n")
        case True
          have "count_honest_node w (Node n l) = 1"
            by (simp add: True \<open>count_honest_node w (Node n l) = of_bool (isHonest w n)\<close>)
          have "ListSum (map (count_honest_node w) l) = 0"
            by (smt One_nat_def Suc_eq_plus1_left True \<open>count_honest_node w (Node n l) = 1\<close> 
add_diff_cancel_left' count_honest_node_def count_node_by_set.elims isHonest_def map_eq_conv nattree.distinct(1) nattree.inject of_bool_eq(2))
          hence "\<forall>x \<in> set l. count_honest_node w x = 0"
            by (metis (full_types) ListSum_0 image_eqI set_map)
          hence "isHonest w m \<longrightarrow> (\<forall>x \<in> set l. count_node m x = 0)"
           using honest_node_0_imp_0_each_honest_node isHonest_def by blast
          hence "isHonest w m \<longrightarrow> count_node m (Node n l) = of_bool (m = n)"
            by (metis \<open>ListSum (map (count_honest_node w) l) = 0\<close> \<open>\<forall>x\<in>set l. count_honest_node w x = 0\<close> 
add_cancel_left_right count_node.simps(2) map_eq_conv)
          hence "isHonest w m \<and> depth (Node n l) m \<noteq> None \<longrightarrow> count_node m (Node n l) \<noteq> 0"
            by (meson zero_exist_imp_none_depth)
          hence  "isHonest w m \<and> depth (Node n l) m \<noteq> None \<longrightarrow> m = n"
            by (metis (full_types) \<open>isHonest w m \<longrightarrow> count_node m (Node n l) = of_bool (m = n)\<close> of_bool_eq(1))
          hence L:"isHonest w m \<and> depth (Node n l) m \<noteq> None \<longrightarrow> depth (Node n l) m = Some 0"
            by (meson depth.simps(2))
          have "m = n \<longrightarrow> depth (Node n (map (\<lambda>x. Empty) l)) m = Some 0"   
            by (meson depth.simps(2))
          hence R:"isHonest w m \<and> depth (Node n l) m \<noteq> None \<longrightarrow> depth (toClosedFork w (Node n l)) m = Some 0"
            using True
            using \<open>count_honest_node w (Node n l) = 1\<close> \<open>isHonest w m \<and> depth (Node n l) m \<noteq> None \<longrightarrow> m = n\<close> by fastforce 
          then show ?thesis using L R
            by (metis (full_types) isFork_toClosedFork_isFork_aux_3_aux none_depth_imp_zero_exist zero_exist_imp_none_depth)
      next
        case False
          have "count_honest_node w (Node n l) = 0"
            by (simp add: False True)
          hence "isHonest w m \<longrightarrow> count_node m (Node n l) = 0"
            using honest_node_0_imp_0_each_honest_node isHonest_def by blast   
          then show ?thesis
            by (metis isFork_toClosedFork_isFork_aux_3_aux zero_exist_imp_none_depth) 
      qed
  next
    case False
      have "toClosedFork w (Node n l) = Node n (map (toClosedFork w) l)" using False
        by simp
      have "count_honest_node w (Node n l) \<noteq> of_bool (isHonest w n)"
        by (simp add: False)
      hence "ListSum (map (count_honest_node w) l) \<noteq> 0"
        by (smt add.right_neutral count_honest_node_def count_node_by_set.simps(2) isHonest_def map_eq_conv)
        (*isHonest w m \<and> depth (Node n l) m \<noteq> None \<longrightarrow> depth (Node n l) m = depth (toClosedFork w (Node n l)) m*)
      then show ?thesis
        by (metis (no_types, lifting) Node.IH \<open>toClosedFork w (Node n l) = Node n (map (toClosedFork w) l)\<close> depth.simps(2) map_eq_map2)         
  qed
qed
    
lemma isFork_toClosedFork_isFork_aux_4 [simp]: 
 "increasing_depth_H F w \<longrightarrow> increasing_depth_H (toClosedFork w F) w"
  by (smt increasing_depth_H.elims(2) increasing_depth_H.elims(3) isFork_toClosedFork_isFork_aux_4_aux isHonest_def)
 

lemma isFork_toClosedFork_isFork_aux_5 [simp]:    
  assumes "root_label_0 F" shows "root_label_0 (toClosedFork w F)"  
proof -
   obtain l where "F = Node 0 l"
     using assms root_label_0.cases by blast
   thus ?thesis
   proof (cases "count_honest_node w (Node 0 l) = 1")
     case True
     hence "toClosedFork w F = Node 0 (map (\<lambda>x. Empty) l)"
       by (metis (full_types) H_0 \<open>F = Node 0 l\<close> isHonest_def of_bool_eq(2) toClosedFork.simps(2))
     then show ?thesis
       by (simp add: \<open>toClosedFork w F = Node 0 (map (\<lambda>x. Empty) l)\<close> root_label_0.intros) 
   next
     case False
       hence "toClosedFork w F = Node 0 (map (toClosedFork w) l)"
         by (metis (full_types) H_0 \<open>F = Node 0 l\<close> count_honest_node_def count_node_by_set.simps(2)
 le_add_same_cancel1 not_one_le_zero of_bool_eq(1) of_bool_eq(2) toClosedFork.simps(2) zero_le)
     then show ?thesis
       by (simp add: \<open>toClosedFork w F = Node 0 (map (toClosedFork w) l)\<close> root_label_0.intros)
   qed
qed
  
lemma isFork_toClosedFork_isFork [simp]: "isFork w F \<longrightarrow> isFork w (toClosedFork w F)"
  using isFork.simps isFork_toClosedFork_isFork_aux_1 isFork_toClosedFork_isFork_aux_2 
isFork_toClosedFork_isFork_aux_3 isFork_toClosedFork_isFork_aux_4 isFork_toClosedFork_isFork_aux_5 by blast
  
lemma toClosedFork_closedFork_aux [simp]: "(closedFork_Hgiven (toClosedFork w F) (H w))"  
proof (induction F)
  case Empty
  then show ?case
    using closedFork_Hgiven.simps(1) toClosedFork.simps(1) by presburger 
next
  case (Node n l)
     hence "\<forall>x \<in> set l. closedFork_Hgiven (toClosedFork w x) (H w)"
       by blast 
     hence "\<forall>x \<in> set (map (toClosedFork w) l). closedFork_Hgiven x (H w)"
       by (metis (mono_tags, hide_lams) imageE set_map)
     hence "\<forall>x \<in> set (map (toClosedFork w) l). (\<lambda>x. closedFork_Hgiven x (H w)) x"
       by blast
     hence f1: "\<forall>x \<in> set (map (\<lambda>x. closedFork_Hgiven x (H w)) (map (toClosedFork w) l)). x"
       by (metis (no_types, lifting) image_iff list.set_map)
  then show ?case 
    proof (cases "count_honest_node w (Node n l) = of_bool (isHonest w n)")
      case True
        hence "count_honest_node w (Node n l) = of_bool (isHonest w n)" by simp
      then show ?thesis 
        proof (cases "isHonest w n")
          case True
            hence "toClosedFork w (Node n l) = Node n (map (\<lambda>x. Empty) l)"
              by (simp add: \<open>count_honest_node w (Node n l) = of_bool (isHonest w n)\<close>)
          then show ?thesis
            by (metis True closedFork_Hgiven.simps(2) isHonest_def map_ListOfEmpty) 
        next
          case False
          then show ?thesis
            using True closedFork_Hgiven.simps(1) toClosedFork.simps(2) by presburger    
        qed
    next
      case False
        hence "toClosedFork w (Node n l) = Node n (map (toClosedFork w) l)"
          by simp
        hence f2:"closedFork_Hgiven (toClosedFork w (Node n l)) (H w) = (if ListOfEmpty (map (toClosedFork w) l) 
                                                                      then (n \<in> (H w)) 
                                                                      else foldr conj (map (\<lambda>x. closedFork_Hgiven x (H w)) (map (toClosedFork w) l)) True)"
          using closedFork_Hgiven.simps(2) by presburger
        have "ListSum (map (count_node_by_set (H w)) l) > 0" using False
          by (simp add: H_def count_honest_node_def isHonest_def)
        obtain child where "child \<in> set l \<and> count_node_by_set (H w) child > 0"
          by (metis ListSum_0 Listmax_ge \<open>0 < ListSum (map (count_node_by_set (H w)) l)\<close> le_zero_eq listmax_0 neq0_conv)
        obtain m bl where "child = Node m bl"
          by (metis \<open>child \<in> set l \<and> 0 < count_node_by_set (H w) child\<close> count_node_by_set.elims neq0_conv)
        hence "toClosedFork w (Node m bl) \<noteq> Empty" 
          proof -
           have "0 < count_honest_node w child"
            using \<open>child \<in> set l \<and> 0 < count_node_by_set (H w) child\<close> count_honest_node_def by presburger
          then show ?thesis
          proof -
            have "\<forall>bs n na. toClosedFork bs n \<noteq> na \<or> Empty = n \<and> Empty = na \<or> (\<exists>nb ns. Node nb ns = n \<and> (count_honest_node bs (Node nb ns) \<noteq> of_bool (isHonest bs nb) \<or> (\<not> isHonest bs nb \<or> Node nb (map (\<lambda>n. Empty) ns) = na) \<and> (isHonest bs nb \<or> Empty = na)) \<and> (count_honest_node bs (Node nb ns) = of_bool (isHonest bs nb) \<or> Node nb (map (toClosedFork bs) ns) = na))"
              by (metis map_eq_map_tailrec nattree.distinct(1) toClosedFork.elims)
            then show ?thesis
              by (metis (no_types) \<open>0 < count_honest_node w child\<close> \<open>child = Node m bl\<close> nattree.simps(3) not_gr_zero of_bool_def)
          qed        
         qed
        hence "\<not> ListOfEmpty (map (toClosedFork w) l)"
          by (metis Leaf.intros Leaf_non_ListOfEmpty \<open>child = Node m bl\<close> \<open>child \<in> set l \<and> 0 < count_node_by_set (H w) child\<close> image_eqI set_map)
        hence "closedFork_Hgiven (toClosedFork w (Node n l)) (H w) = foldr conj (map (\<lambda>x. closedFork_Hgiven x (H w)) (map (toClosedFork w) l)) True"
          using f2 by presburger
        then show ?thesis using f1 foldr_conj_eq_forall
          by blast
    qed
qed

lemma toClosedFork_closedFork [simp]: "isFork w F \<longrightarrow> closedFork (toClosedFork w F) w"  
proof (cases F)
  case Empty
  then show ?thesis
    using closedFork_Hgiven.simps(1) closedFork_def toClosedFork.simps(1) by presburger 
next
  case (Node n l)
    then show ?thesis
      using closedFork_def isFork_toClosedFork_isFork toClosedFork_closedFork_aux by blast 
qed
   
lemma length_langest_tine_eq_height_aux_0 [simp]: "x \<in> set_of_tines F \<longrightarrow> length x \<le> height F"
  by (simp add: set_of_tines_def)
  
lemma length_langest_tine_eq_height_aux_1 [simp]: "\<exists> x \<in> set_of_tines F. length x = height F"
 proof (induction F)
   case Empty
   then show ?case by simp
 next
   case (Node n l)
   then show ?case
     proof (cases "Leaf (Node n l)")
       case True
       then show ?thesis
         by (metis height.simps(2) list.size(3) nil_in_set_of_tines) 
     next
       case False
        hence "height (Node n l) = Suc (ListMax (map height l))"
          by (meson height.simps(2))
        obtain y where "y \<in> set (map height l) \<and> y = ListMax (map height l)"
          by (metis False Leaf.intros ListMax_member ListOfEmpty.Nil list.map_disc_iff)
        then obtain a where "a \<in> set l \<and> a \<noteq> Empty \<and> height a = ListMax (map height l)"
          by (metis (no_types, lifting) False Leaf_non_ListOfEmpty Listmax_ge height.simps(1) imageE image_eqI le_0_eq set_map)
        then obtain b where "b \<in> set_of_tines a \<and> length b = height a"
          using Node.IH by blast
        then obtain m where "m < length l \<and> nth l m = a"
          by (meson \<open>a \<in> set l \<and> a \<noteq> Empty \<and> height a = ListMax (map height l)\<close> in_set_conv_nth)
        then obtain nn ll where "a = Node nn ll"
          using \<open>a \<in> set l \<and> a \<noteq> Empty \<and> height a = ListMax (map height l)\<close> max_node.cases by blast
        then have "getLabelFromTine (Node n l) (m#b) = nn#(getLabelFromTine a b)"
          by (metis \<open>m < length l \<and> l ! m = a\<close> getLabelFromTine.simps(3) nattree.simps(5) not_less)
          then show ?thesis
            by (metis \<open>a \<in> set l \<and> a \<noteq> Empty \<and> height a = ListMax (map height l)\<close> \<open>b \<in> set_of_tines a \<and> length b = height a\<close> \<open>height (Node n l) = Suc (ListMax (map height l))\<close> \<open>m < length l \<and> l ! m = a\<close> getLabelFromTine_branch_in_if length_Cons) 
         
     qed
 qed
    
lemma length_langest_tine_eq_height [simp]: "(\<forall>x \<in> set_of_tines F. length x \<le> height F) \<and> (\<exists>x \<in> set_of_tines F. length x = height F)"
  using length_langest_tine_eq_height_aux_1 by auto
  
lemma exist_Some_eq_ListMaxOption_ne_None [simp]: "(\<exists>x. Some x \<in> set l) \<longleftrightarrow> ListMaxOption l \<noteq> None"
  by auto     
    
lemma ListMaxOption_Max_Some [simp]: "ListMaxOption l = None \<or> (\<exists>x. ListMaxOption l = Some x \<and> Some x \<in> set l \<and> (\<forall>y. Some y \<in> set l \<longrightarrow> y \<le> x))" 
  proof (induction l)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
    then show ?case 
      proof (cases x)
        case None
          have "ListMaxOption (None#xs) = ListMaxOption xs"
            by (simp add: ListMaxOption_def)
        then show ?thesis
          by (metis Cons.IH None insert_iff list.simps(15) option.distinct(1))
      next
        case (Some M)
          hence "x = Some M"
            by simp
        then show ?thesis 
          proof (cases "ListMaxOption xs")
            case None
              hence "ListMaxOption (x#xs) = Some M"
                by (simp add: ListMaxOption_def Some)
            then show ?thesis
              by (metis None Some eq_iff exist_Some_eq_ListMaxOption_ne_None option.inject set_ConsD) 
          next
            case (Some a)
            then show ?thesis 
              proof (cases "a < M")
                case True
                hence "ListMaxOption (x#xs) = Some M"
                  using ListMaxOption_def Some \<open>x = Some M\<close> by auto
                then show ?thesis
                  using Cons.IH Some True \<open>x = Some M\<close> by auto 
              next
                case False
                  hence "ListMaxOption (x#xs) = Some a"
                  using ListMaxOption_def Some \<open>x = Some M\<close> by auto
                then show ?thesis
                  using Cons.IH Some False \<open>x = Some M\<close> by auto 
          qed
      qed
  qed
qed
  
lemma depth_le_height [simp]: "count_node x F = 0 \<or> le_option (depth F x) (Some (height F))"    
 proof (induction F)
 case Empty
   then show ?case
    by simp 
 next
   case (Node n l)
   then show ?case 
     proof (cases "count_node x (Node n l) = 0")
       case True
       then show ?thesis by blast
     next
       case False
         hence "count_node x (Node n l) \<noteq> 0"
           by simp
         have "\<forall>y \<in> set l. count_node x y = 0 \<or> le_option (depth y x) (Some (height y))"
           using Node.IH by blast
         have "\<forall>y \<in> set l. count_node x y = 0 \<longrightarrow> depth y x = None"
           using zero_exist_imp_none_depth by blast
         hence "\<forall>y \<in> set l. count_node x y = 0 \<longrightarrow> \<not> le_option (depth y x) (Some (height y))"
           by (metis le_option.cases option.simps(3))
         hence f1:"depth (Node n l) x = (if n = x 
                          then (Some 0) 
                          else SucOption (ListMaxOption (map (\<lambda>y. depth y x) l)))"
           using depth.simps(2) by blast
         then show ?thesis 
           proof (cases "n=x")
             case True
             then show ?thesis
               using \<open>depth (Node n l) x = (if n = x then Some 0 else SucOption (ListMaxOption (map (\<lambda>y. depth y x) l)))\<close> le0 le_option.intros by presburger 
           next
             case False
               then obtain w where w:"(ListMaxOption (map (\<lambda>y. depth y x) l)) = Some w \<and> Some w \<in> set (map (\<lambda>y. depth y x) l)"
                 by (metis (no_types, lifting) False ListMaxOption_Max_Some SucOption_def 
\<open>count_node x (Node n l) \<noteq> 0\<close> f1 none_depth_imp_zero_exist option.simps(4))
               then obtain y where "y \<in> set l \<and> depth y x = Some w"
                 by (metis imageE set_map)    
               have "depth (Node n l) x = Some (Suc w)" using w
                 by (metis False SucOption_def \<open>depth (Node n l) x = (if n = x then Some 0 else 
SucOption (ListMaxOption (map (\<lambda>y. depth y x) l)))\<close> option.simps(5))
               have "le_option (depth y x) (Some (height y))"
                 by (metis Node.IH \<open>\<forall>y\<in>set l. count_node x y = 0 \<longrightarrow> depth y x = None\<close> \<open>y \<in> set l \<and> depth y x = Some w\<close> option.distinct(1))
               hence "w \<le> height y"
                 by (metis \<open>y \<in> set l \<and> depth y x = Some w\<close> le_option.cases option.inject)
               hence "Suc (height y) \<le> height (Node n l)"
                 by (metis Leaf_non_ListOfEmpty Listmax_ge \<open>\<forall>y\<in>set l. count_node x y = 0 \<longrightarrow> 
\<not> le_option (depth y x) (Some (height y))\<close> \<open>le_option (depth y x) (Some (height y))\<close> \<open>y \<in> set l \<and> 
depth y x = Some w\<close> count_node.simps(1) height.simps(2) image_eqI not_less_eq_eq set_map)
               then show ?thesis
                 by (metis \<open>depth (Node n l) x = Some (Suc w)\<close> \<open>w \<le> height y\<close> le_option.intros le_trans not_less_eq_eq) 
           qed           
     qed
 qed

fun max_exist_honest_node :: "nattree \<Rightarrow> bool list \<Rightarrow> nat" where
  "max_exist_honest_node Empty _ = 0"
| "max_exist_honest_node (Node n l) w = 
(if isHonest w n 
then max n (ListMax (map (\<lambda>x. max_exist_honest_node x w) l)) 
else ListMax (map (\<lambda>x. max_exist_honest_node x w) l))"    

lemma max_exist_honest_node_isHonest [simp]: "isHonest w (max_exist_honest_node F w)"
  proof (induction F)
    case Empty
    then show ?case 
      using H_0 isHonest_def max_exist_honest_node.simps(1) by presburger 
  next
    case (Node n l)
      hence 1:"max_exist_honest_node (Node n l) w = (if isHonest w n 
                then max n (ListMax (map (\<lambda>x. max_exist_honest_node x w) l)) 
                else ListMax (map (\<lambda>x. max_exist_honest_node x w) l))"
        by simp
      hence 2: "isHonest w n \<longrightarrow> max_exist_honest_node (Node n l) w = max n (ListMax (map (\<lambda>x. max_exist_honest_node x w) l))"
        by simp    
      hence "isHonest w n \<longrightarrow>  max_exist_honest_node (Node n l) w = n \<or> max_exist_honest_node (Node n l) w = ListMax (map (\<lambda>x. max_exist_honest_node x w) l)"
        by linarith
    then show ?case
      by (metis (no_types, lifting) "1" H_0 ListMax_0 ListMax_member Node.IH imageE isHonest_def set_map)
  qed
  
lemma  exist_le_real_max [simp]: "max_exist_honest_node F w \<le> max_honest_node w" 
proof (induction F)
  case Empty
  then show ?case
    by simp
next
  case (Node n l)
    hence f1:"max_exist_honest_node (Node n l) w = (if isHonest w n 
then max n (ListMax (map (\<lambda>x. max_exist_honest_node x w) l)) 
else ListMax (map (\<lambda>x. max_exist_honest_node x w) l))"
      by simp 
    have f2:"ListMax (map (\<lambda>x. max_exist_honest_node x w) l) \<le> max_honest_node w"
      by (metis (no_types, lifting) ListMax_member Node gr_implies_not_zero imageE leI list.map_disc_iff 
listmax_0 max_exist_honest_node.simps(1) set_map)
  have f3 :"isHonest w n \<longrightarrow> n \<le> max_honest_node w"
    by (metis Sup_fin.bounded_iff Sup_fin_Max equals0D finite_honest_node isHonest_def le_refl max_honest_node_def)
  then show ?case using f1 f2 f3 by simp
qed

lemma max_exist_honest_node_ge_branches [simp]: "\<forall>x \<in> set l. max_exist_honest_node (Node n l) w \<ge> max_exist_honest_node x w"
proof -
  have "max_exist_honest_node (Node n l) w = (if isHonest w n 
        then max n (ListMax (map (\<lambda>x. max_exist_honest_node x w) l)) 
        else ListMax (map (\<lambda>x. max_exist_honest_node x w) l))"
    by auto
  have "\<forall>y \<in> set (map (\<lambda>x. max_exist_honest_node x w) l). max n (ListMax (map (\<lambda>x. max_exist_honest_node x w) l)) \<ge> y"
    using Listmax_ge max.coboundedI2 by blast   
  hence f1:"\<forall>y \<in> set l. max n (ListMax (map (\<lambda>x. max_exist_honest_node x w) l)) \<ge> max_exist_honest_node y w"
    by simp
  hence "max n (ListMax (map (\<lambda>x. max_exist_honest_node x w) l)) \<ge> max_exist_honest_node (Node n l) w"
    by auto
  thus ?thesis using f1
    by simp
qed
      
lemma isFork_max_exist_honest_node_eq_max_honest_node [simp]: 
"count_node (max_honest_node w) F \<noteq> 0 \<longrightarrow> max_exist_honest_node F w = max_honest_node w" 
proof (induction F) 
  case Empty 
  then show ?case 
    by simp 
next
  case (Node n l)
  then show ?case 
  proof (cases "(max_honest_node w) = n")
    case True
      hence "count_node (max_honest_node w) (Node n l) > 0"
        by simp
      hence f1:"max_exist_honest_node (Node n l) w = (if isHonest w n 
then max n (ListMax (map (\<lambda>x. max_exist_honest_node x w) l)) 
else ListMax (map (\<lambda>x. max_exist_honest_node x w) l)) "
        by simp
      have "isHonest w n" using True
        by (metis H_0 Max_in equals0D finite_honest_node isHonest_def max_honest_node_def)
      hence "max_exist_honest_node (Node n l) w = max n (ListMax (map (\<lambda>x. max_exist_honest_node x w) l))"
        using f1 by simp
    then show ?thesis
      by (metis True exist_le_real_max max.commute max_def) 
  next
    case False
      hence unfold:"max_exist_honest_node (Node n l) w = (if isHonest w n 
then max n (ListMax (map (\<lambda>x. max_exist_honest_node x w) l)) 
else ListMax (map (\<lambda>x. max_exist_honest_node x w) l)) " by simp
      have if_lt:"isHonest w n \<longrightarrow> n < max_honest_node w"
      proof -
        { assume "\<not> n \<le> 0"
          { assume "\<not> n \<le> \<Squnion>\<^sub>f\<^sub>i\<^sub>n{n. n \<le> length w \<and> \<not> (False # w) ! n} \<and> \<not> n \<le> 0"
            then have "max_exist_honest_node (Node n []) w \<noteq> max n 0"
              by (metis H_def Sup_fin_Max exist_le_real_max max_def max_honest_node_def)
            then have ?thesis
              by auto }
          then have "n \<le> \<Squnion>\<^sub>f\<^sub>i\<^sub>n{n. n \<le> length w \<and> \<not> (False # w) ! n} \<or> (isHonest w n \<longrightarrow> n < max_honest_node w)"
            by blast }
        then have "n \<le> \<Squnion>\<^sub>f\<^sub>i\<^sub>n{n. n \<le> length w \<and> \<not> (False # w) ! n} \<or> n < \<Squnion>\<^sub>f\<^sub>i\<^sub>n{n. n \<le> length w \<and> \<not> (False # w) ! n} \<or> (isHonest w n \<longrightarrow> n < max_honest_node w)"
          by blast
        then show ?thesis
          by (metis False H_def Sup_fin_Max le_neq_implies_less max_honest_node_def)
      qed
      hence "count_node (max_honest_node w) (Node n l) \<noteq> 0 \<longrightarrow> ListSum (map (count_node (max_honest_node w)) l) \<noteq> 0"
        using False by simp
      hence f1:"count_node (max_honest_node w) (Node n l) \<noteq> 0 \<longrightarrow> (\<exists>x \<in> set l. count_node (max_honest_node w) x \<noteq> 0)"
        by (metis ListSum_0 imageE image_set)
      hence f2:"count_node (max_honest_node w) (Node n l) \<noteq> 0 \<longrightarrow> (\<exists>x \<in> set l. max_exist_honest_node x w = max_honest_node w)"
        using Node.IH by blast
      hence f3: "count_node (max_honest_node w) (Node n l) \<noteq> 0 \<longrightarrow> (\<exists>x \<in> set (map (\<lambda>y. max_exist_honest_node y w) l). x = max_honest_node w)"
        by (metis (full_types) image_eqI set_map)
      hence f4:"count_node (max_honest_node w) (Node n l) \<noteq> 0 \<longrightarrow> (\<forall>x \<in> set (map (\<lambda>y. max_exist_honest_node y w) l). x \<le> max_honest_node w)"
        by simp
      hence f5:"count_node (max_honest_node w) (Node n l) \<noteq> 0 \<longrightarrow> max_honest_node w \<le> ListMax (map (\<lambda>x. max_exist_honest_node x w) l)" using f1 f2
         Listmax_ge f3 by blast
      hence "count_node (max_honest_node w) (Node n l) \<noteq> 0 \<longrightarrow> ListMax (map (\<lambda>x. max_exist_honest_node x w) l) \<le> max_honest_node w" using f4 ListMax_member
        by (metis ListMax_0 le0)
    then show ?thesis using f5 if_lt
      by fastforce
  qed
qed
  
lemma max_exist_honest_node_is_max [simp]: "\<forall>x \<in> H w. x > max_exist_honest_node F w \<longrightarrow> count_node x F = 0" 
  proof (induction F)
    case Empty
    then show ?case
      using count_node.simps(1) by blast 
  next
    case (Node n l)
      hence "\<forall>x \<in> set l. max_exist_honest_node (Node n l) w \<ge> max_exist_honest_node x w"
        using max_exist_honest_node_ge_branches by blast
      have "\<forall>x \<in> H w. x > max_exist_honest_node (Node n l) w \<longrightarrow> (\<forall>z \<in> set l. count_node x z = 0)"
        by (meson Node.IH le_less_trans max_exist_honest_node_ge_branches) 
      have "max n (ListMax (map (\<lambda>x. max_exist_honest_node x w) l)) \<ge> n"
        using max.cobounded1 by blast
      hence "n \<in> H w \<longrightarrow> max_exist_honest_node (Node n l) w \<ge> n"
        using isHonest_def max_exist_honest_node.simps(2) by presburger
      hence "n \<in> H w \<longrightarrow> (\<forall>x \<in> H w. x > max_exist_honest_node (Node n l) w \<longrightarrow> count_node x(Node n l) = 0)"
        by (smt ListSum_0 Suc_leI \<open>\<forall>x\<in>H w. max_exist_honest_node (Node n l) w < x \<longrightarrow> (\<forall>z\<in>set l. count_node x z = 0)\<close> 
add.left_neutral count_node.simps(2) imageE not_less_eq_eq of_bool_eq(1) set_map)
      then show ?case
      by (smt ListSum_0 \<open>\<forall>x\<in>H w. max_exist_honest_node (Node n l) w < x \<longrightarrow> (\<forall>z\<in>set l. count_node x z = 0)\<close> 
add_is_0 count_node.simps(2) imageE of_bool_eq(1) set_map) 
  qed
  
definition H_tree_and_string :: "nattree \<Rightarrow> bool list \<Rightarrow> nat set" where
  "H_tree_and_string t w= {x. x \<in> H w \<and> count_node x t > 0}"

lemma max_exist_honest_member_H_tree_and_string [simp]: "max_exist_honest_node F w \<in> H_tree_and_string F w \<or> max_exist_honest_node F w = 0"
  proof (induction F)
    case Empty
    then show ?case by auto
  next
    case (Node n l)
    then show ?case 
      proof (cases "max_exist_honest_node (Node n l) w = n")
        case True
          hence "isHonest w n"
            by (metis max_exist_honest_node_isHonest) 
        then show ?thesis
        proof -
          have "0 < count_node n (Node n l)"
            by simp
          then have "n \<in> {na \<in> H w. 0 < count_node na (Node n l)}"
            using \<open>isHonest w n\<close> isHonest_def by blast
          then show ?thesis
            using H_tree_and_string_def True by presburger
        qed 
      next
        case False
          hence f1:"max_exist_honest_node (Node n l) w = ListMax (map (\<lambda>x. max_exist_honest_node x w) l)"
            by (smt map_eq_conv max_def max_exist_honest_node.simps(2))        
          then show ?thesis 
            proof (cases "l = Nil")
              case True
              then show ?thesis
                by (metis ListMax_0 \<open>max_exist_honest_node (Node n l) w = ListMax (map (\<lambda>x. max_exist_honest_node x w) l)\<close> list.simps(8)) 
            next
              case False
                then obtain x where x:"x \<in> set l \<and> max_exist_honest_node x w = ListMax (map (\<lambda>x. max_exist_honest_node x w) l)"
                  by (metis (no_types, lifting) ListMax_member imageE image_set map_is_Nil_conv)
                hence "max_exist_honest_node x w \<in> H_tree_and_string x w \<or> max_exist_honest_node x w = 0"
                  by (meson Node.IH)
                have "max_exist_honest_node x w = max_exist_honest_node (Node n l) w"
                  using f1 x by linarith
                hence "max_exist_honest_node (Node n l) w \<in> H_tree_and_string x w \<or> max_exist_honest_node (Node n l) w = 0"
                  using \<open>max_exist_honest_node x w \<in> H_tree_and_string x w \<or> max_exist_honest_node x w = 0\<close> by presburger
              then show ?thesis
                by (smt H_tree_and_string_def ListSum_ge One_nat_def Suc_leI count_node.simps(2) gr0I 
image_eqI image_set le_trans mem_Collect_eq not_one_le_zero x zero_eq_add_iff_both_eq_0) 
            qed
      qed
  qed
  
lemma max_exist_honest_node_ge_member_H_tree_and_string [simp]: "(\<forall>x \<in> H_tree_and_string F w. max_exist_honest_node F w \<ge> x)"
  proof (induction F)
    case Empty
    then show ?case
      using H_tree_and_string_def count_node.simps(1) gr_implies_not0 by blast 
  next
    case (Node n l)
    then show ?case 
      proof (cases "max_exist_honest_node (Node n l) w = n")
        case True
          hence "n \<ge> ListMax (map (\<lambda>x. max_exist_honest_node x w) l)"
            by (metis max.coboundedI2 max_exist_honest_node.elims nat_le_linear nattree.distinct(1) nattree.inject)
          hence "\<forall>x \<in> H_tree_and_string (Node n l) w. x = n \<or> (\<exists> z \<in> set l. max_exist_honest_node z w \<ge> x)"
            by (smt H_tree_and_string_def ListSum_0 Node.IH add_is_0 count_node.simps(2) gr_implies_not_zero 
imageE image_set leI le_zero_eq mem_Collect_eq of_bool_eq(1))
        then show ?thesis
          by (metis True eq_iff le_trans max_exist_honest_node_ge_branches) 
      next
        case False
        hence "max_exist_honest_node (Node n l) w = ListMax (map (\<lambda>x. max_exist_honest_node x w) l)"
          by (smt map_eq_conv max_def max_exist_honest_node.simps(2))
        hence "n \<in> H_tree_and_string (Node n l) w \<longrightarrow> max_exist_honest_node (Node n l) w > n"
          by (metis (no_types, lifting) False H_tree_and_string_def isHonest_def le_max_iff_disj le_neq_implies_less le_refl max_exist_honest_node.simps(2) mem_Collect_eq)
          hence "\<forall>x \<in> H_tree_and_string (Node n l) w. x = n \<or> (\<exists> z \<in> set l. max_exist_honest_node z w \<ge> x)"
            by (smt H_tree_and_string_def ListSum_0 Node.IH add_is_0 count_node.simps(2) gr_implies_not_zero 
imageE image_set leI le_zero_eq mem_Collect_eq of_bool_eq(1))
          then show ?thesis
            by (metis \<open>n \<in> H_tree_and_string (Node n l) w \<longrightarrow> n < max_exist_honest_node (Node n l) w\<close> 
dual_order.strict_iff_order max.bounded_iff max_def max_exist_honest_node_ge_branches) 
       qed
  qed
  
definition uniqueH_nodes_in_tree :: "nattree \<Rightarrow> bool list \<Rightarrow> bool" where
  "uniqueH_nodes_in_tree t l =(\<forall>x \<in> H l. count_node x t \<le> 1)"
   
lemma ind_uniqueH_nodes_in_tree [simp]: 
"uniqueH_nodes_in_tree (Node n l) w \<longrightarrow> (\<forall>x \<in> set l. uniqueH_nodes_in_tree x w)"
proof -
  have "uniqueH_nodes_in_tree (Node n l) w = (\<forall>x \<in> H w. count_node x (Node n l) \<le> 1)"
    using uniqueH_nodes_in_tree_def by blast
  hence "uniqueH_nodes_in_tree (Node n l) w = (\<forall>x \<in> H w. (of_bool (n = x)) + ListSum (map (count_node x) l) \<le> 1)"
    by (smt count_node.simps(2))
  hence "uniqueH_nodes_in_tree (Node n l) w \<longrightarrow> (\<forall>x \<in> H w. ListSum (map (count_node x) l) \<le> 1)"
    using le_add2 le_trans by blast
  hence "uniqueH_nodes_in_tree (Node n l) w \<longrightarrow> (\<forall>x \<in> H w. \<forall>y \<in> set l. count_node x y \<le> 1)"
    by (metis (no_types, lifting) ListSum_ge dual_order.trans image_eqI image_set)
  then show ?thesis
    using uniqueH_nodes_in_tree_def by blast
qed   

lemma ind_increasing_depth_H_tree_string_aux_exist [simp]:    
  assumes "count_node x (Node n l) = 1" 
  shows "((depth (Node n l) x = Some 0 \<and> n = x) 
 \<or>
(\<exists>d. \<exists>z \<in> set l. depth (Node n l) x = Some (Suc d) \<and> 
depth z x = Some d \<and> count_node x z = 1))"
proof (cases "n =x")
  case True
  then show ?thesis
    by (meson depth.simps(2)) 
next
  case False
    then obtain d where d:"depth (Node n l) x = Some (Suc d)"
      by (metis SucOption_def assms depth.simps(2) none_depth_imp_zero_exist option.case_eq_if zero_neq_one)
   have "depth (Node n l) x = ( SucOption (ListMaxOption (map (\<lambda>y. depth y x) l)))" using False
     using depth.simps(2) by presburger
   hence "ListMaxOption (map (\<lambda>y. depth y x) l) = Some d" using d
     by (smt ListMaxOption_Max_Some SucOption_def Suc_eq_plus1_left add_diff_cancel_left' option.inject option.simps(4) option.simps(5))
   then obtain z where z:"z \<in> set l \<and> depth z x = Some d"
     by (metis ListMaxOption_Max_Some imageE image_set option.simps(3))
   hence "count_node x z > 0"
     by (metis neq0_conv option.simps(3) zero_exist_imp_none_depth)
   hence "count_node x z \<le> 1" using assms
     by (smt False ListSum_ge One_nat_def Suc_eq_plus1 z add_diff_cancel_left' count_node.simps(2) image_eqI image_set of_bool_eq(1))
   hence "count_node x z = 1"
     using \<open>0 < count_node x z\<close> by linarith
  then show ?thesis using d z by blast
qed

lemma ind_increasing_depth_H_tree_string_aux_all [simp]:    
  "count_node x (Node n l) = 1 \<and> depth (Node n l) x = Some (Suc d)
  \<longrightarrow> (\<forall>z \<in> set l. count_node x z = 1 \<longrightarrow> 
depth z x = Some d)"
proof (rule ccontr)
    assume assm:"\<not> (count_node x (Node n l) = 1 \<and> depth (Node n l) x = Some (Suc d) \<longrightarrow>
        (\<forall>z\<in>set l. count_node x z = 1 \<longrightarrow> depth z x = Some d))"
    then obtain z1 where z1: "z1 \<in> set l \<and> count_node x z1 = 1 \<and> depth z1 x \<noteq> Some d"
      by blast
    hence "x = n \<longrightarrow> count_node x (Node n l) > 1"
      by (metis assm depth.simps(2) nat.discI option.inject)
    hence ne:"x \<noteq> n"
      using assm by linarith 
    obtain d1 where d1:"z1 \<in> set l \<and> count_node x z1 = 1 \<and> depth z1 x = Some d1 \<and> d1 \<noteq> d"
      using z1 by (metis depth_le_height le_option.cases zero_neq_one)
    have "depth (Node n l) x = (if n = x then (Some 0) 
                          else SucOption (ListMaxOption (map (\<lambda>y. depth y x) l)))"
      by simp
    hence "depth (Node n l) x = SucOption (ListMaxOption (map (\<lambda>y. depth y x) l))"
      using ne
      by presburger
    hence "(ListMaxOption (map (\<lambda>y. depth y x) l) = Some d) \<and> d1 \<le> d" 
      using d1 ListMaxOption_Max_Some SucOption_ne_Some_0
      by (smt SucOption_def assm image_eqI image_set nat.inject option.inject option.simps(3) option.simps(4) option.simps(5)) 
    obtain z where "z \<in> set l \<and> count_node x z = 1 \<and> depth z x = Some d" using assm
     using ne
     by (metis assm diff_Suc_1 ind_increasing_depth_H_tree_string_aux_exist option.inject)    
    hence "z \<noteq> z1  \<and> count_node x z = 1  \<and> count_node x z1 = 1" using z1
      by blast
    hence "(count_node x (Node n l) > 1)" using ListSum_ge_lifting_2
      by (smt \<open>x = n \<longrightarrow> 1 < count_node x (Node n l)\<close> \<open>z \<in> set l \<and> count_node x z = 1 \<and> depth z x = Some d\<close> assm comm_monoid_add_class.add_0 count_node.simps(2) discrete of_bool_eq(1)) 
    thus "False"
      using assm by linarith    
qed    
  
lemma lt_option_R_ne_Some_0 [simp]: assumes "lt_option x y" shows "y \<noteq> Some 0"
  using assms lt_option.simps by blast
  
lemma ind_increasing_depth_H_tree_string [simp]: 
"((uniqueH_nodes_in_tree (Node n l) w) \<and> (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
\<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) \<longrightarrow> 
(\<forall> z \<in> set l . (uniqueH_nodes_in_tree z w) \<and> (\<forall> x y. x \<in> (H_tree_and_string z w) \<and> y \<in> (H_tree_and_string z w) \<and> x < y \<longrightarrow> lt_option (depth z x) (depth z y)))"  
proof -
  have "uniqueH_nodes_in_tree (Node n l) w \<longrightarrow> (\<forall>x \<in> set l. uniqueH_nodes_in_tree x w)" by simp
  hence "uniqueH_nodes_in_tree (Node n l) w \<and> isHonest w n \<longrightarrow> count_node n (Node n l) = 1 \<and> ListSum (map (count_node n) l) = 0"
    by (smt add_diff_cancel_left' count_node.simps(2) diff_is_0_eq eq_iff isHonest_def le_add1 of_bool_eq(2) uniqueH_nodes_in_tree_def)
  have "\<forall> z \<in> set l . (H_tree_and_string z w) \<subseteq> (H_tree_and_string (Node n l) w)"
    by (smt H_tree_and_string_def ListSum_ge add_is_0 count_node.simps(2) eq_iff gr_zeroI image_eqI image_set less_imp_le_nat mem_Collect_eq subsetI)
  hence "(\<forall>x \<in> (H_tree_and_string (Node n l) w). \<exists>d. Some d = (depth (Node n l) x))"
    by (metis (no_types, lifting) H_tree_and_string_def mem_Collect_eq none_depth_imp_zero_exist not_less0 option.collapse)
  have "\<forall>x. (if n = x then (Some 0) else SucOption (ListMaxOption (map (\<lambda>y. depth y x) l))) = Some 0 \<longrightarrow> n = x"
    by (meson SucOption_ne_Some_0) 
  hence some0:"(\<forall>x \<in> (H_tree_and_string (Node n l) w). (depth (Node n l) x) = Some 0 \<longrightarrow> n = x)"
    by (metis depth.simps(2)) 
  hence "(uniqueH_nodes_in_tree (Node n l) w) \<longrightarrow> (\<forall>x \<in> (H_tree_and_string (Node n l) w). count_node x (Node n l) = 1)"
    by (metis (no_types, lifting) H_tree_and_string_def less_one mem_Collect_eq nat_less_le uniqueH_nodes_in_tree_def)
  hence  "(uniqueH_nodes_in_tree (Node n l) w) \<longrightarrow> (\<forall>x \<in> (H_tree_and_string (Node n l) w). (depth (Node n l) x) \<noteq> Some 0 \<longrightarrow>
(\<exists>d. \<exists>z \<in> set l.(depth (Node n l) x) = Some (Suc d) \<and> depth z x = Some d \<and> count_node x z = 1))"
    using ind_increasing_depth_H_tree_string_aux_exist by blast 
  hence "(uniqueH_nodes_in_tree (Node n l) w) \<longrightarrow> 
(\<forall>x y. \<forall> z \<in> set l. lt_option (depth (Node n l) x) (depth (Node n l) y) \<and> x \<in> (H_tree_and_string z w) \<and> y \<in> (H_tree_and_string z w) 
\<longrightarrow>  lt_option (depth z x) (depth z y))" 
  proof -
    have "(uniqueH_nodes_in_tree (Node n l) w) \<longrightarrow> 
(\<forall>x y. \<forall> z \<in> set l. lt_option (depth (Node n l) x) (depth (Node n l) y) \<and> x \<in> (H_tree_and_string z w) \<and> y \<in> (H_tree_and_string z w) 
\<longrightarrow> (depth (Node n l) y) \<noteq> Some 0)"
      using lt_option_R_ne_Some_0 by blast
    hence "(uniqueH_nodes_in_tree (Node n l) w) \<longrightarrow> 
(\<forall>x y. \<forall> z \<in> set l. lt_option (depth (Node n l) x) (depth (Node n l) y) \<and> x \<in> (H_tree_and_string z w) \<and> y \<in> (H_tree_and_string z w) 
\<longrightarrow> y \<noteq> n)"
      by (metis depth.simps(2))
    hence "(uniqueH_nodes_in_tree (Node n l) w) \<longrightarrow> 
(\<forall>x y. \<forall> z \<in> set l. lt_option (depth (Node n l) x) (depth (Node n l) y) \<and> x \<in> (H_tree_and_string z w) \<and> y \<in> (H_tree_and_string z w) 
\<longrightarrow> x \<noteq> n)"
      by (metis (no_types, lifting) H_tree_and_string_def ListSum_ge \<open>uniqueH_nodes_in_tree (Node n l) w 
\<and> isHonest w n \<longrightarrow> count_node n (Node n l) = 1 \<and> ListSum (map (count_node n) l) = 0\<close> image_eqI isHonest_def le_zero_eq mem_Collect_eq not_less0 set_map)
    hence "(uniqueH_nodes_in_tree (Node n l) w) \<longrightarrow> 
(\<forall>x y. \<forall> z \<in> set l. lt_option (depth (Node n l) x) (depth (Node n l) y) \<and> x \<in> (H_tree_and_string z w) \<and> y \<in> (H_tree_and_string z w) 
\<longrightarrow> lt_option (depth z x) (depth z y))" using  ind_increasing_depth_H_tree_string_aux_exist ind_increasing_depth_H_tree_string_aux_all
      by (smt H_tree_and_string_def Suc_leI \<open>uniqueH_nodes_in_tree (Node n l) w \<longrightarrow> (\<forall>x\<in>set l. uniqueH_nodes_in_tree x w)\<close> 
le_neq_implies_less less_one lt_option.intros lt_option.simps mem_Collect_eq not_less0 not_less_eq option.inject option.simps(3) uniqueH_nodes_in_tree_def zero_exist_imp_none_depth)
    thus ?thesis
      by blast
  qed
  then show ?thesis
    using \<open>\<forall>z\<in>set l. H_tree_and_string z w \<subseteq> H_tree_and_string (Node n l) w\<close> \<open>uniqueH_nodes_in_tree (Node n l) w \<longrightarrow> (\<forall>x\<in>set l. uniqueH_nodes_in_tree x w)\<close> by blast 
qed    

lemma max_exist_honest_node_count_node_positive [simp]: "(count_node (max_exist_honest_node F w) F > 0) \<or> (max_exist_honest_node F w = 0)"
  proof (induction F)
    case Empty
    then show ?case sorry
  next
    case (Node x1 x2)
    then show ?case sorry
  qed    
    
lemma colsedFork_height_eq_depth_max_honest_aux [simp]: 
"closedFork_Hgiven F (H w) \<and> (uniqueH_nodes_in_tree F w) \<and>
(\<forall> x y. x \<in> (H_tree_and_string F w) \<and> y \<in> (H_tree_and_string F w) \<and> x < y \<longrightarrow> lt_option (depth F x) (depth F y)) 
\<longrightarrow> (Some (height F) = depth F (max_exist_honest_node F w) \<or> F = Empty)"
proof (induction F)
  case Empty
  then show ?case
    by blast 
next
  case (Node n l)
    hence "((uniqueH_nodes_in_tree (Node n l) w) \<and> (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
\<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) \<longrightarrow> 
(\<forall> z \<in> set l . (uniqueH_nodes_in_tree z w) \<and> (\<forall> x y. x \<in> (H_tree_and_string z w) \<and> y \<in> (H_tree_and_string z w) \<and> x < y \<longrightarrow> lt_option (depth z x) (depth z y)))"
     using ind_increasing_depth_H_tree_string
     by blast 
    hence "closedFork_Hgiven (Node n l) (H w) \<longrightarrow> (\<forall>z \<in> set l. closedFork_Hgiven z (H w))"
      using closedFork_Hgiven_imp_branches by blast
    hence "(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
\<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) \<longrightarrow> 
(\<forall> z \<in> set l . closedFork_Hgiven z (H w) \<and> (uniqueH_nodes_in_tree z w) \<and> (\<forall> x y. x \<in> (H_tree_and_string z w) \<and> y \<in> (H_tree_and_string z w) \<and> x < y \<longrightarrow> lt_option (depth z x) (depth z y)))"
      using \<open>uniqueH_nodes_in_tree (Node n l) w \<and> (\<forall>x y. x \<in> H_tree_and_string (Node n l) w \<and> 
y \<in> H_tree_and_string (Node n l) w \<and> x < y \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y)) 
\<longrightarrow> (\<forall>z\<in>set l. uniqueH_nodes_in_tree z w \<and> (\<forall>x y. x \<in> H_tree_and_string z w \<and> y \<in> H_tree_and_string z w \<and> x < y \<longrightarrow> lt_option (depth z x) (depth z y)))\<close> by blast
    hence ih:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
\<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) \<longrightarrow>
(\<forall> z \<in> set l. (Some (height z) = depth z (max_exist_honest_node z w) \<or> z = Empty)) "
      using Node.IH by blast
    then show ?case 
      proof (cases "n = max_exist_honest_node (Node n l) w")
        case True
          hence "n = max_exist_honest_node (Node n l) w" by blast
          hence "isHonest w n"
            by (metis max_exist_honest_node_isHonest) 
          have "0 < count_node n (Node n l)"
            by simp
          hence nexisthonest:"n \<in> (H_tree_and_string (Node n l) w)"
            using H_tree_and_string_def \<open>isHonest w n\<close> isHonest_def by blast
          hence le:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
(\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
\<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) \<longrightarrow> (\<forall>z \<in> set l. max_exist_honest_node z w \<le> n)"
            by (metis True max_exist_honest_node_ge_branches)
           hence cn0:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
(\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
\<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) \<longrightarrow> (\<forall>z \<in> set l. count_node n z = 0)" using True nexisthonest
             by (smt ListSum_0 One_nat_def \<open>0 < count_node n (Node n l)\<close> \<open>isHonest w n\<close> add_diff_cancel_left' 
count_node.simps(2) diff_Suc_1 image_eqI isHonest_def nat_less_le not_less_eq of_bool_eq(2) set_map uniqueH_nodes_in_tree_def)
            hence lt:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
(\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
\<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) \<longrightarrow> (\<forall>z \<in> set l. max_exist_honest_node z w < n \<or> n = 0)"
              by (metis le less_numeral_extra(3) max_exist_honest_node_count_node_positive order.not_eq_order_implies_strict)
            then show ?thesis 
            proof (cases "n = 0")
              case True
                hence lt:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
(\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
\<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) \<longrightarrow> (\<forall>z \<in> set l. max_exist_honest_node z w = 0)"
                using le by blast
                hence lt:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
(\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
\<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) \<longrightarrow> (\<forall>z \<in> set l. z = Empty)"
                  by (metis True ih cn0 option.simps(3) zero_exist_imp_none_depth)
                then show ?thesis
                    by (metis Leaf_non_ListOfEmpty \<open>n = max_exist_honest_node (Node n l) w\<close> depth.simps(2) height_Leaf) 
            next
              case False
                hence "(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
(\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
\<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) \<longrightarrow> (\<forall>z \<in> set l. max_exist_honest_node z w < n)"
                  using lt by blast
                have "n \<in> H_tree_and_string (Node n l) w"
                  by (simp add: nexisthonest)
                have "depth (Node n l) n = Some 0"
                  by simp                    
                hence "(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
(\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
\<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) \<longrightarrow> (\<forall>z \<in> set l. max_exist_honest_node z w > 0 
\<longrightarrow> count_node (max_exist_honest_node z w) z > 0)"
                  by (metis less_irrefl_nat max_exist_honest_node_count_node_positive)
                hence "(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
(\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
\<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) \<longrightarrow> (\<forall>z \<in> set l. count_node (max_exist_honest_node z w) z > 0 
\<longrightarrow> max_exist_honest_node z w \<in> H_tree_and_string (Node n l) w)"
                  by (smt H_tree_and_string_def ListSum_ge add_diff_cancel_left' count_node.simps(2) 
diff_is_0_eq image_eqI isHonest_def less_or_eq_imp_le max_exist_honest_node_isHonest mem_Collect_eq not_gr_zero not_le set_map)
                hence "(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
(\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
\<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) \<longrightarrow> (\<forall>z \<in> set l. count_node (max_exist_honest_node z w) z = 0)"
                  using \<open>closedFork_Hgiven (Node n l) (H w) \<and> uniqueH_nodes_in_tree (Node n l) w \<and> 
(\<forall>x y. x \<in> H_tree_and_string (Node n l) w \<and> y \<in> H_tree_and_string (Node n l) w \<and> x < y \<longrightarrow> lt_option 
(depth (Node n l) x) (depth (Node n l) y)) \<longrightarrow> (\<forall>z\<in>set l. max_exist_honest_node z w < n)\<close> 
\<open>depth (Node n l) n = Some 0\<close> lt_option_R_ne_Some_0 nexisthonest by blast
                hence "(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
(\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
\<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) \<longrightarrow> (\<forall>z \<in> set l. z = Empty)"
                  by (metis ih option.simps(3) zero_exist_imp_none_depth)
                then show ?thesis
                  by (metis True \<open>depth (Node n l) n = Some 0\<close> height.simps(2) not_Leaf_imp_not_List_of_empty) 
            qed
      next
        case False
          hence "n \<noteq> max_exist_honest_node (Node n l) w"
            by simp 
          hence "max_exist_honest_node (Node n l) w = (if isHonest w n 
then max n (ListMax (map (\<lambda>x. max_exist_honest_node x w) l)) 
else ListMax (map (\<lambda>x. max_exist_honest_node x w) l))"
            by simp              
          hence "max_exist_honest_node (Node n l) w = ListMax (map (\<lambda>x. max_exist_honest_node x w) l)"
            using False by presburger
          hence existorempty:"(\<exists>z \<in> set (map (\<lambda>x. max_exist_honest_node x w) l). max_exist_honest_node (Node n l) w = z) \<or> ListOfEmpty l"
            using ListMax_member ListOfEmpty.simps by blast
          then show ?thesis 
          proof (cases "ListOfEmpty l")
            case True
            then show ?thesis
              by (metis False Leaf.intros Leaf_non_ListOfEmpty \<open>max_exist_honest_node (Node n l) w = 
(if isHonest w n then max n (ListMax (map (\<lambda>x. max_exist_honest_node x w) l)) else ListMax (map (\<lambda>x. max_exist_honest_node x w) l))\<close> 
closedFork_Hgiven.simps(2) isHonest_def le_0_eq listmax_0 max_def max_exist_honest_node.simps(1)) 
          next
            case False
              hence "(\<exists>z \<in> set l. z \<noteq> Empty)"
                using not_ListOfEmpty_imp_not_Empty_existence by blast 
              hence "(\<exists>z \<in> set (map (\<lambda>x. max_exist_honest_node x w) l). max_exist_honest_node (Node n l) w = z)"
                using False existorempty by blast
              hence exist:"(\<exists>z \<in> set l. max_exist_honest_node (Node n l) w =  max_exist_honest_node z w)"
                by (metis (no_types, lifting) imageE image_set)
              hence all :" (\<forall>z \<in> set l. max_exist_honest_node z w \<in> H_tree_and_string (Node n l) w \<or> max_exist_honest_node z w = 0)"
                by (metis (full_types, lifting) H_tree_and_string_def ListSum_ge add_is_0 count_node.simps(2) 
image_eqI le_zero_eq max_exist_honest_member_H_tree_and_string mem_Collect_eq not_gr_zero set_map) 
                then show ?thesis 
                proof (cases "max_exist_honest_node (Node n l) w = 0")
                  case True
                    hence "(\<forall>z \<in> set l. max_exist_honest_node z w = 0)"
                      by (metis (full_types) eq_iff le0 max_exist_honest_node_ge_branches)
                    then obtain z1 where "z1 \<in> set l \<and> max_exist_honest_node z1 w = 0"
                      using \<open>\<exists>z\<in>set l. z \<noteq> Empty\<close> by blast
                    hence "(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
(\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
\<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) \<longrightarrow> count_node 0 (Node n l) > 0"
                      by (metis (no_types, lifting) ListSum_ge \<open>\<exists>z\<in>set l. z \<noteq> Empty\<close> \<open>\<forall>z\<in>set l. max_exist_honest_node z w = 0\<close> 
add_is_0 count_node.simps(2) gr_zeroI ih image_eqI image_set leD option.distinct(1) zero_exist_imp_none_depth)
                     hence f1:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
(\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
\<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) \<longrightarrow> count_node 0 (Node n l) = 1"
                       by (metis H_0 One_nat_def Suc_mono le_less_Suc_eq uniqueH_nodes_in_tree_def)
                    hence f2:"(\<forall>y \<in> H w. y > 0 \<longrightarrow> count_node y (Node n l) = 0)" using True
                      by (metis max_exist_honest_node_is_max)
                    hence f3:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>z \<in> set l. count_node 0 z \<noteq> 0)" using f1 False zero_exist_imp_none_depth ih
                      by (metis True \<open>n \<noteq> max_exist_honest_node (Node n l) w\<close> ind_increasing_depth_H_tree_string_aux_exist zero_neq_one)
                         hence f4: "(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>z \<in> set l. count_node 0 z = 1)" using f1
                           by (metis (mono_tags, hide_lams) True \<open>n \<noteq> max_exist_honest_node (Node n l) w\<close> ind_increasing_depth_H_tree_string_aux_exist)
                         hence f5:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>z \<in> set l. count_node 0 z = 1 \<and> (\<forall>z' \<in> set l. count_node 0 z' = 1 \<longrightarrow> z =z'))" using f1
                           by (metis unique_node_branches unique_node_def)                   
                         hence f6:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>z \<in> set l. count_node 0 z = 1 \<and> Some (height z) = depth z 0 \<and> (\<forall>z' \<in> set l. count_node 0 z' = 1 \<longrightarrow> depth z' 0 = depth z 0))" using True f4 ih
                           by (metis \<open>\<forall>z\<in>set l. max_exist_honest_node z w = 0\<close> count_node.simps(1) zero_neq_one)
                         hence f7: "(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>z \<in> set l. count_node 0 z = 1 \<and> Some (height z) = depth z 0 \<and> (\<forall>z' \<in> set l. count_node 0 z' = 1 \<longrightarrow> depth z' 0 = depth z 0))
                        \<and> (\<forall>z \<in> set l. count_node 0 z \<le> 1)"  using True f4 ih
                           using H_0 \<open>closedFork_Hgiven (Node n l) (H w) \<and> uniqueH_nodes_in_tree (Node n l) w \<and> 
(\<forall>x y. x \<in> H_tree_and_string (Node n l) w \<and> y \<in> H_tree_and_string (Node n l) w \<and> x < y \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y)) 
\<longrightarrow> (\<forall>z\<in>set l. closedFork_Hgiven z (H w) \<and> uniqueH_nodes_in_tree z w \<and> (\<forall>x y. x \<in> H_tree_and_string z w \<and> y \<in> H_tree_and_string z w \<and> x < y 
\<longrightarrow> lt_option (depth z x) (depth z y)))\<close> uniqueH_nodes_in_tree_def by blast
                        hence f8:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<forall>z \<in> set l. (count_node 0 z = 1 \<and> Some (height z) = depth z 0) \<or> (count_node 0 z = 0 \<and> z = Empty))" using True f4 ih
                          by (metis One_nat_def \<open>\<forall>z\<in>set l. max_exist_honest_node z w = 0\<close> count_node.simps(1) 
le_eq_less_or_eq less_SucE less_nat_zero_code max_exist_honest_node_ge_member_H_tree_and_string option.discI zero_exist_imp_none_depth)
                        hence f9: "(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<forall>z \<in> set l. (count_node 0 z = 1 \<and> Some (height z) = depth z 0) \<or> 
                      (count_node 0 z = 0 \<and> z = Empty \<and> depth z 0 = None))" using True f4 ih
                          by (meson zero_exist_imp_none_depth)                         
                        hence f10:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>h. \<forall>z \<in> set l. (count_node 0 z = 1 \<and> Some h = depth z 0) \<or> 
                      (count_node 0 z = 0 \<and> depth z 0 = None))" using True f4 ih f5 f7 f8
                          by smt
                        hence f11:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>h. \<forall>z \<in> set l. (count_node 0 z = 1 \<and> Some h = depth z 0 \<and> h = height z) \<or> 
                      (count_node 0 z = 0 \<and> depth z 0 = None))" using True f4 ih f5 f7 f8
                          by smt 
                          hence f12:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>h. \<forall>z \<in> set l. (count_node 0 z = 1 \<and> height z = h \<and> Some h = depth z 0) \<or> (count_node 0 z = 0 \<and> z = Empty))"
                            by (smt f5 f8) 
                         hence f13:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>h. \<forall>z \<in> set l. (count_node 0 z = 1 \<and> height z = h \<and> Some h = depth z 0) \<or> (count_node 0 z = 0 \<and> z = Empty) 
                          \<and> (\<exists>z \<in> set l. (count_node 0 z = 1 \<and> height z = h \<and> Some h = depth z 0)))"
                           using \<open>\<exists>z\<in>set l. z \<noteq> Empty\<close> by blast
                         hence f14:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>h. \<forall>z \<in> set l. (count_node 0 z = 1 \<and> height z = h \<and> Some h = depth z 0) \<or> (count_node 0 z = 0 \<and> z = Empty) 
                          \<and> (\<exists>z \<in> set l. (count_node 0 z = 1 \<and> height z = h \<and> Some h = depth z 0))) \<and> n \<noteq> 0"
                           using True \<open>n \<noteq> max_exist_honest_node (Node n l) w\<close> by presburger
                         hence f15:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>h. \<forall>z \<in> set l. (count_node 0 z = 1 \<and> height z = h \<and> Some h = depth z 0) \<or> (count_node 0 z = 0 \<and> z = Empty \<and> depth z 0 = None) 
                          \<and> (\<exists>z \<in> set l. (count_node 0 z = 1 \<and> height z = h \<and> Some h = depth z 0))) \<and> n \<noteq> 0"
                           by (meson zero_exist_imp_none_depth)         
                         hence f16:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> ListMaxOption (map (\<lambda>x. depth x 0) l) = None \<or> (\<exists>x. ListMaxOption (map (\<lambda>x. depth x 0) l) = Some x 
                      \<and> Some x \<in> set (map (\<lambda>x. depth x 0) l) \<and> (\<forall>y. Some y \<in> set (map (\<lambda>x. depth x 0) l) \<longrightarrow> y \<le> x))" 
                           using f7 exist_Some_eq_ListMaxOption_ne_None ListMaxOption_Max_Some
                           by meson
                         hence f17:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>z \<in> set l. depth z 0 \<noteq> None)" using f10 f3 f15 H_def H_tree_and_string_def
                               by (meson none_depth_imp_zero_exist)
                         hence f18:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>x. ListMaxOption (map (\<lambda>x. depth x 0) l) = Some x 
                      \<and> Some x \<in> set (map (\<lambda>x. depth x 0) l) \<and> (\<forall>y. Some y \<in> set (map (\<lambda>x. depth x 0) l) \<longrightarrow> y \<le> x))" 
                           using f7 exist_Some_eq_ListMaxOption_ne_None ListMaxOption_Max_Some
                           by (smt SucOption_def depth.simps(2) f1 f15 map_eq_conv none_depth_imp_zero_exist option.simps(4) zero_neq_one)
                          hence f19:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>x. ListMaxOption (map (\<lambda>x. depth x 0) l) = Some x 
                      \<and> Some x \<in> set (map (\<lambda>x. depth x 0) l) \<and> (\<forall>y. Some y \<in> set (map (\<lambda>x. depth x 0) l) \<longrightarrow> y \<le> x))" 
                            by blast 
                          hence f20:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>x. ListMaxOption (map (\<lambda>x. depth x 0) l) = Some x 
                      \<and> Some x \<in> set (map (\<lambda>x. depth x 0) l) \<and> (\<forall>y. Some y \<in> set (map (\<lambda>x. depth x 0) l) \<longrightarrow> y \<le> x))
                      \<and> (\<exists>h. \<forall>z \<in> set l. (count_node 0 z = 1 \<and> height z = h \<and> Some h = depth z 0) \<or> (count_node 0 z = 0 \<and> z = Empty) 
                          \<and> (\<exists>z \<in> set l. (count_node 0 z = 1 \<and> height z = h \<and> Some h = depth z 0)))" 
                            using f15
                            by meson
                        hence f21:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>x. ListMaxOption (map (\<lambda>x. depth x 0) l) = Some x \<and> (\<forall>y. Some y \<in> set (map (\<lambda>x. depth x 0) l) \<longrightarrow> y \<le> x)
                      \<and> Some x \<in> set (map (\<lambda>x. depth x 0) l) \<and> (\<exists>z \<in> set l. (count_node 0 z = 1 \<and> height z = x \<and> Some x = depth z 0)))" using f10 imageE option.sel option.simps(3) set_map list.set_map option.discI
                          by (smt f6)
                         hence f22:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>z \<in> set l. ListMaxOption (map (\<lambda>x. depth x 0) l) = Some (height z))"                         
                           by metis              
                         hence f23:"(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>z \<in> set l. ListMaxOption (map (\<lambda>x. depth x 0) l) = Some (height z) 
\<and> (\<exists>y \<in> set l. height z < height y \<longrightarrow> ListMaxOption (map (\<lambda>x. depth x 0) l) \<noteq> Some (height z))) "
                           by blast   
                         hence f24 : "(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> (\<exists>z \<in> set l. ListMaxOption (map (\<lambda>x. depth x 0) l) = Some (height z) 
                      \<and> (\<forall> y \<in> set l. height z \<ge> height y))"
                           by (metis f21 f20 height.simps(1) less_eq_nat.simps(1) zero_neq_one)
                         hence f25 : "(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> ListMaxOption (map (\<lambda>x. depth x 0) l) = Some (ListMax (map height l))"
                           by (metis (no_types, lifting) False ListMax_member ListOfEmpty.simps Listmax_ge 
f21 f22 imageE image_eqI le_antisym map_is_Nil_conv set_map)  
                             hence f26 : "(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) 
                      \<longrightarrow> depth (Node n l) 0 = Some (Suc (ListMax (map height l)))"
                               by (smt f1 f15 f21 f6 ind_increasing_depth_H_tree_string_aux_exist option.sel)
                      then show ?thesis using f15
                        by (metis Leaf_non_ListOfEmpty True \<open>\<exists>z\<in>set l. z \<noteq> Empty\<close> height.simps(2))
                next
                  case False
                    hence "max_exist_honest_node (Node n l) w > 0"
                      by simp                                                                               
                    hence "max_exist_honest_node (Node n l) w =  ListMax (map (\<lambda>x. max_exist_honest_node x w) l)"
                      using \<open>max_exist_honest_node (Node n l) w = ListMax (map (\<lambda>x. max_exist_honest_node x w) l)\<close> by blast
                    then obtain z where z:"z \<in> set l \<and> max_exist_honest_node (Node n l) w = max_exist_honest_node z w"
                      using exist by blast
                    hence f1:"(uniqueH_nodes_in_tree (Node n l) w) \<longrightarrow> (\<forall>y \<in> set l. count_node (max_exist_honest_node (Node n l) w) y \<le> 1)"
                      using ind_uniqueH_nodes_in_tree isHonest_def max_exist_honest_node_isHonest uniqueH_nodes_in_tree_def by blast
                    hence f2:"(uniqueH_nodes_in_tree (Node n l) w) \<longrightarrow> (\<forall>y \<in> set l. count_node (max_exist_honest_node (Node n l) w) y = 1 \<longrightarrow> y = z)"
                    proof -
                      { fix nn :: nattree
                        have ff1: "max_exist_honest_node z w \<noteq> 0"
                          by (metis False \<open>z \<in> set l \<and> max_exist_honest_node (Node n l) w = max_exist_honest_node z w\<close>)
                        have ff2: "\<And>na. na \<notin> set l \<or> max_exist_honest_node na w = 0 \<or> max_exist_honest_node na w \<in> H w \<and> 0 < count_node (max_exist_honest_node na w) (Node n l)"
                          using H_tree_and_string_def all by blast
                        have ff3: "\<And>n bs. count_node (max_exist_honest_node n bs) n \<noteq> 0 \<or> max_exist_honest_node n bs = 0"
                          using max_exist_honest_node_count_node_positive not_gr_zero by blast
                        have "count_node (max_exist_honest_node z w) (Node n l) \<noteq> 0"
                          using ff1 by (metis \<open>z \<in> set l \<and> max_exist_honest_node (Node n l) w = max_exist_honest_node z w\<close> max_exist_honest_node_count_node_positive not_gr_zero)
                        then have "count_node (max_exist_honest_node z w) nn = 1 \<longrightarrow> nn = z \<or> nn \<notin> set l \<or> \<not> uniqueH_nodes_in_tree (Node n l) w \<or> count_node (max_exist_honest_node (Node n l) w) nn \<noteq> 1"
                          using ff3 ff2 ff1 by (meson \<open>z \<in> set l \<and> max_exist_honest_node (Node n l) w = max_exist_honest_node z w\<close> ind_uniqueH_nodes_in_tree le_neq_implies_less less_one uniqueH_nodes_in_tree_def unique_node_branches unique_node_def)
                        then have "nn = z \<or> nn \<notin> set l \<or> \<not> uniqueH_nodes_in_tree (Node n l) w \<or> count_node (max_exist_honest_node (Node n l) w) nn \<noteq> 1"
                          by (metis \<open>z \<in> set l \<and> max_exist_honest_node (Node n l) w = max_exist_honest_node z w\<close>) }
                      then show ?thesis
                        by meson
                    qed
                    hence f3:"(uniqueH_nodes_in_tree (Node n l) w) \<longrightarrow> (\<forall>y \<in> set l. y \<noteq> z \<longrightarrow> count_node (max_exist_honest_node (Node n l) w) y = 0)"
                      using f1 le_neq_implies_less by blast    
                    hence f4:"(uniqueH_nodes_in_tree (Node n l) w) \<longrightarrow> (\<forall>y \<in> set l. y \<noteq> z \<longrightarrow> max_exist_honest_node y w < max_exist_honest_node z w)"
                      by (metis False z le_neq_implies_less less_numeral_extra(3) max_exist_honest_node_count_node_positive max_exist_honest_node_ge_branches)      
                    hence f5: "(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) \<longrightarrow>  
(\<forall>y \<in> set l. (y \<noteq> z \<and> (lt_option (depth (Node n l) (max_exist_honest_node y w)) (depth (Node n l) (max_exist_honest_node z w)) \<or> max_exist_honest_node y w = 0)) 
               \<or> y = z)"
                      by (metis False all z)
                    hence f6: "(closedFork_Hgiven (Node n l) (H w) \<and> (uniqueH_nodes_in_tree (Node n l) w) \<and> 
                      (\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y 
                      \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))) \<longrightarrow>  
(\<forall>y \<in> set l. (y \<noteq> z \<and> (lt_option (depth (Node n l) (max_exist_honest_node y w)) (depth (Node n l) (max_exist_honest_node z w)))
\<or> ((Some (height y) = depth y 0 \<and>  max_exist_honest_node y w = 0) \<or> y = Empty)) 
               \<or> y = z)"
                      by (metis ih)
                              
                  then show ?thesis sorry
                qed
          qed
      qed
qed

lemma closedFork_height_eq_depth_max_honest [simp]: "closedFork F w \<longrightarrow> Some (height F) = depth F (max_honest_node w)"
proof (cases F)
  case Empty
  then show ?thesis
    by (metis closedFork_def depth.simps(1) isFork.simps option.discI root_label_0_depth_0) 
next
  case (Node n l)
  hence f0:"closedFork (Node n l) w \<longrightarrow> (isFork w (Node n l) \<and> closedFork_Hgiven (Node n l) (H w))"
    using closedFork_def by blast
  hence f1:"closedFork (Node n l) w \<longrightarrow> (isFork w (Node n l) \<and> closedFork_Hgiven (Node n l) (H_tree_and_string (Node n l) w))"
    by (smt Collect_cong H_def H_tree_and_string_def gr0I isFork_uniqueH_tree mem_Collect_eq of_bool_eq(1) of_bool_eq(2) of_bool_eq_iff unique_node_def)
  hence f2:"closedFork (Node n l) w \<longrightarrow> (uniqueH_nodes_in_tree (Node n l) w)"
    by (metis isFork_uniqueH_tree less_or_eq_imp_le uniqueH_nodes_in_tree_def unique_node_def)    
  have f3:"closedFork (Node n l) w \<longrightarrow> (uniqueH_tree (Node n l) w \<and> increasing_depth_H (Node n l) w \<and> closedFork_Hgiven (Node n l) (H_tree_and_string (Node n l) w))"
    using f1 isFork.simps by blast
  hence "closedFork (Node n l) w \<longrightarrow>  closedFork_Hgiven (Node n l) (H_tree_and_string (Node n l) w) \<and> 
(\<forall> x y. x \<in> (H_tree_and_string (Node n l) w) \<and> y \<in> (H_tree_and_string (Node n l) w) \<and> x < y \<longrightarrow> lt_option (depth (Node n l) x) (depth (Node n l) y))"
    by (metis (no_types, lifting) H_tree_and_string_def increasing_depth_H.simps mem_Collect_eq)
  then show ?thesis
    by (metis H_0 Max_in Node f2 f3 closedFork_def colsedFork_height_eq_depth_max_honest_aux equals0D 
finite_honest_node isFork_max_exist_honest_node_eq_max_honest_node max_honest_node_def nattree.simps(3) 
uniqueH_tree_def unique_node_def unique_nodes_by_nat_set.elims(2) zero_neq_one)
qed 
 
lemma closedFork_longest_tine_end_max_honest [simp]: "closedFork F w \<longrightarrow> 
(\<exists>x \<in> set_of_tines F. Some (length x) = depth F (max_honest_node w) \<and> (\<forall>y \<in> set_of_tines F - {x}. length y < length x))"
  sorry
    
(*trying to find the way to describe the longest honest prefix 
then use it to show that after the last node there are only adversarial ones
and the length of original one is greater than or equal to the height now
so the number of suffix adversarial nodes is greater than the different of the gap

*)
    
lemma exist_longest_honest_prefix_tine [simp]: 
"t \<in> set_of_tines F \<and> t \<noteq> [] \<and> isFork w F\<longrightarrow> 
(\<exists>x. (isPrefix_tine F F t x) \<and> isHonest w (last x) \<and> (\<forall>y. isPrefix_tine F F t y \<and> isHonest w (last y) \<longrightarrow> length y < length x))"  
  sorry
  
lemma toClosedFork_prefixFork [simp]: "isFork w F \<longrightarrow> isPrefix_fork w w F (toClosedFork w F)"
  sorry   
    
lemma closedFork_deepest_honest_node_eq_height [simp]: "closedFork F w \<longrightarrow> 
depth (toClosedFork w F) (max_honest_node w) = Some (height F)"
  sorry
    
definition honestTine :: "nattree \<Rightarrow> bool list \<Rightarrow> nat list \<Rightarrow> bool" where
  "honestTine t w tine = ((tine \<in> set_of_tines t) \<and> (getLabelFromTine t tine = [] \<or> isHonest w (last (getLabelFromTine t tine))))"

lemma toClosedFork_honest_tines_biggest [simp]: 
"isFork w F \<longrightarrow> (\<forall>tine \<in> set_of_tines F. honestTine F w tine \<longrightarrow> tine \<in> set_of_tines (toClosedFork w F))"    
  sorry
   
lemma toClosedFork_height_le [simp]: 
"height (toClosedFork w F) \<le> height F"
  sorry
   
lemma obtain_two_non_negative_reach_tines_toClosedFork [simp]: 
  assumes "isFork w F" and "flatFork w F" and "\<not> ListOfAdverse w" 
  shows "(\<exists> (t1,t2) \<in> set_of_edge_disjoint_tines (toClosedFork w F).
reach (toClosedFork w F) w t1 \<ge> 0 
\<and> reach (toClosedFork w F) w t2 \<ge> 0)"  
proof -
  have "closedFork (toClosedFork w F) w"
    using assms(1) toClosedFork_closedFork by blast
  have "(\<exists> t1 \<in> set_of_tines F.  \<exists> t2 \<in> set_of_tines F. 
 length t1 = length t2 \<and> length t1 = height F \<and> edge_disjoint_tines t1 t1)"
    using assms(2) flatFork_def flatTree_def by blast
 show ?thesis    
 sorry
qed
  
lemma min_reach_image [simp]: "(\<lambda>x. min (reach F' w (fst x)) (reach F' w (snd x)))`(set_of_edge_disjoint_tines F') 
= {r. (\<exists> (a,b) \<in> set_of_edge_disjoint_tines F'. r = min (reach F' w a) (reach F' w b))}"
  by (smt Collect_cong case_prod_unfold image_def)
  
  
lemma if_4_17 [simp]: assumes "isForkable w" shows  "(\<exists> F.(isFork w F \<and> margin F w \<ge> 0))"
proof (cases "ListOfAdverse w")
  case True
  then show ?thesis
    using margin_no_honest by blast 
next
  case False
  obtain F where F:"isFork w F \<and> flatFork w F"
    using assms flatFork_def isForkable_def by blast 
  then obtain F' where "F' = toClosedFork w F"
    by blast
  then obtain t1 and t2 where "(t1,t2) \<in> set_of_edge_disjoint_tines F' \<and> reach F' w t1 \<ge> 0 \<and> reach F' w t2 \<ge> 0" 
    using F False obtain_two_non_negative_reach_tines_toClosedFork by blast
  hence ge_0:"min (reach F' w t1) (reach F' w t2) \<ge> 0" by simp
  hence isin:"min (reach F' w t1) (reach F' w t2) \<in> {r. (\<exists> (a,b) \<in> set_of_edge_disjoint_tines F'. r = min (reach F' w a) (reach F' w b))}"
    using \<open>(t1, t2) \<in> set_of_edge_disjoint_tines F' \<and> 0 \<le> reach F' w t1 \<and> 0 \<le> reach F' w t2\<close> by auto
  have "(\<lambda>x. min (reach F' w (fst x)) (reach F' w (snd x)))`(set_of_edge_disjoint_tines F') 
= {r. (\<exists> (a,b) \<in> set_of_edge_disjoint_tines F'. r = min (reach F' w a) (reach F' w b))}" 
    by (smt Collect_cong case_prod_unfold image_def)
  hence finite: "finite {r. (\<exists> (a,b) \<in> set_of_edge_disjoint_tines F'. r = min (reach F' w a) (reach F' w b))}"
    using set_of_edge_disjoint_tines_finite by auto
  hence "Max {r. (\<exists> (a,b) \<in> set_of_edge_disjoint_tines F'. r = min (reach F' w a) (reach F' w b))} \<ge> min (reach F' w t1) (reach F' w t2) " using isin
    by (simp add: isin)
  hence "margin F' w \<ge> min (reach F' w t1) (reach F' w t2)" using margin_def by simp
  then show ?thesis using ge_0 F
    by (smt \<open>F' = toClosedFork w F\<close> isFork_toClosedFork_isFork) 
qed
   
lemma only_if_4_17 [simp]: assumes  "(\<exists> F.(isFork w F \<and> margin F w \<ge> 0))" shows " isForkable w"
proof (cases "ListOfAdverse w")
  case True
  then show ?thesis
    using Leaf.intros ListOfEmpty.Nil flatFork_Trivial forkable_eq_exist_flatfork by blast 
next
  case False
  then show ?thesis sorry
qed
  
proposition proposition_4_17 : "isForkable w \<longleftrightarrow> (\<exists> F.(isFork w F \<and> margin F w \<ge> 0))"
  using if_4_17 only_if_4_17 by blast 
 
definition lambda_of_string :: "bool list \<Rightarrow> int" where   
  "lambda_of_string w = Max {t. (\<exists>F.(isFork w F \<and> closedFork F w \<and> t = lambda F w))}"

lemma max_node_lowerbound : "max_node (Node n l) \<ge> n" by simp 
 
lemma max_node_lowerbound_branch : "(\<exists> x \<in> set l. x = Node n ll) \<longrightarrow> max_node (Node m l) \<ge> n "
  by (metis Listmax_ge dual_order.trans image_eqI list.set_intros(2) max_node.simps(2) max_node_lowerbound set_map)

lemma isFork_Nil : assumes "isFork [] F" shows "Leaf F \<and> root_label_0 F"
proof -
  have inc : "increasing_tree F" 
    using assms isFork_increasing_tree by blast
  have root0:  "root_label_0 F"
    using assms isFork_root_0 by blast
  then obtain l where Fnode:  "F = Node 0 l"
    using root_label_0.cases by blast
  then have "\<not> ListOfEmpty l \<longrightarrow> (\<exists> x \<in> set l. x \<noteq> Empty)"
    using not_ListOfEmpty_imp_not_Empty_existence by blast 
  then have "\<not> ListOfEmpty l \<longrightarrow> (\<exists> n. (\<exists>ll. Node n ll \<in> set l))"
    by (metis \<open>F = Node 0 l\<close> assms increasing_tree_ind isFork_increasing_tree lt_nat_tree.elims(2))
  then have "\<not> ListOfEmpty l \<longrightarrow> (\<exists> n. n > 0 \<and> (\<exists>ll. Node n ll \<in> set l))"
    using Fnode inc increasing_tree_ind lt_nat_tree.simps(2) by blast
  then have "\<not> ListOfEmpty l \<longrightarrow> (max_node F > 0)"
    by (metis Fnode gr0I max_node_lowerbound_branch not_le)
  then show ?thesis
    by (metis Fnode Leaf.intros assms isFork_max_not_exceed list.size(3) not_le root0) 
qed
    
lemma label_from_Leaf_eq_nil : assumes "Leaf t" shows "getLabelFromTine t x = []"
  by (metis Leaf.cases Leaf_imp_nil_label_tine assms)
  
lemma reserve_nil_nil : "reserve [] [] = 0" 
  by (simp add: reserve_def)

lemma lambda_of_nil_aux : assumes "isFork [] F \<and> closedFork F []" shows "lambda F [] = 0"   
proof -
  have f1: "Leaf F \<and> root_label_0 F"
    using assms isFork_Nil by blast 
  then have " reach F [] [] =  int (reserve [] (getLabelFromTine F [])) - int (gap F [])"
    using reach_def by blast
  then have "reach F [] [] = int (reserve [] []) - int 0"
    using f1 gap_def height_Leaf label_from_Leaf_eq_nil by presburger
  then have "reach F [] [] = 0"
    using reserve_nil_nil  by presburger 
  then show "lambda F [] = 0"
  proof - 
    have "\<forall>x. getLabelFromTine F x = []"
      using f1 label_from_Leaf_eq_nil by blast
    then have "set_of_tines F = {tine. length tine = 0}"
      using set_of_tines_def by auto
    then have set_nil:"set_of_tines F = {[]}"
      by auto
    then have "(\<forall> x \<in> set_of_tines F. reach F [] x = 0)"
      using f1 by (metis \<open>reach F [] [] = 0\<close> singletonD)
    have "(\<exists> x \<in> set_of_tines F. reach F [] x = 0)"
      using set_nil \<open>reach F [] [] = 0\<close> by blast
    have "Max {r. \<exists> x \<in> set_of_tines F. r = reach F [] x} = 0"
      using \<open>reach F [] [] = 0\<close> set_nil by auto
    then show ?thesis
      using lambda_def by auto
 qed
qed 

lemma lambda_of_nil : "lambda_of_string [] = 0"  
proof -
  obtain F where F:"isFork [] F"
    using ListOfAdverse.Nil margin_no_honest by blast 
  then have f1: "Leaf F \<and> root_label_0 F" 
    by (metis isFork_Nil)
  have "closedFork F []" 
    using f1 ListOfAdverse.Nil closedFork_ListOfAdverse root_label_0.cases by blast      
  obtain ss where ss:"ss = {t. \<exists>f. isFork [] f \<and> closedFork f [] \<and> t = lambda f []}"
    by blast 
  then have zero_in: "ss = {0}"
    by (smt Collect_cong F \<open>closedFork F []\<close> lambda_of_nil_aux singleton_conv2)
  then have "Max ss = 0"
    by simp
  have "Max {i. \<exists>n. isFork [] n \<and> closedFork n [] \<and> i = lambda n []} = 0"
      using \<open>Max ss = 0\<close> ss by blast
  then show ?thesis
      using lambda_of_string_def by presburger
qed
    
definition margin_of_string :: "bool list \<Rightarrow> int" where
  "margin_of_string w = Max {t. (\<exists>F.(isFork w F \<and> closedFork F w \<and> t = margin F w))}"

lemma margin_of_nil_aux :  assumes "isFork [] F \<and> closedFork F []" shows "margin F [] = 0"   
proof -
  have f1: "Leaf F \<and> root_label_0 F"
    using assms isFork_Nil by blast 
  then have " reach F [] [] =  int (reserve [] (getLabelFromTine F [])) - int (gap F [])"
    using reach_def by blast
  then have "reach F [] [] = int (reserve [] []) - int 0"
    using f1 gap_def height_Leaf label_from_Leaf_eq_nil by presburger
  then have reach0:"reach F [] [] = 0"
    using reserve_nil_nil  by presburger 
  have "\<forall>x. getLabelFromTine F x = []"
    using f1 label_from_Leaf_eq_nil by blast
  then have "set_of_tines F = {tine. length tine = 0}"
    by (simp add: set_of_tines_def)
  then have "set_of_tines F = {[]}"
    by auto
  then have "\<forall>x \<in> set_of_tines F . x =  [] "
    by auto
    have "edge_disjoint_tines [] []"
     by simp
    then have "set_of_edge_disjoint_tines F = 
       {(x,y). x \<in> set_of_tines F \<and> y \<in> set_of_tines F}"
     using \<open>set_of_tines F = {[]}\<close> set_of_edge_disjoint_tines_def by auto
    then have all:"\<forall> (a,b) \<in> set_of_edge_disjoint_tines F. (a,b) = ([],[])"
      using \<open>\<forall>x\<in>set_of_tines F. x = []\<close> by auto
    have exist: "\<exists> (a,b) \<in> set_of_edge_disjoint_tines F. (a,b) = ([],[])"
      using \<open>set_of_edge_disjoint_tines F = {(x, y). x \<in> set_of_tines F \<and> y \<in> set_of_tines F}\<close> \<open>set_of_tines F = {[]}\<close> by blast
    hence set_nil_pair:"set_of_edge_disjoint_tines F={([],[])}"
      using all by blast  
    have "Max {r. (\<exists> (a,b) \<in> set_of_edge_disjoint_tines F. r = min (reach F [] a) (reach F [] b))} = 0"
        using reach0 set_nil_pair by auto  
    thus ?thesis using margin_def
      by simp
qed 
  
lemma margin_of_nil: "margin_of_string [] = 0"
  proof -
  obtain F where "isFork [] F"
    using ListOfAdverse.Nil margin_no_honest by blast 
  then have f1: "Leaf F \<and> root_label_0 F" 
    by (metis isFork_Nil)
  have "closedFork F []" 
    using f1 ListOfAdverse.Nil closedFork_ListOfAdverse root_label_0.cases by blast   
   obtain ss where ss:"ss = {t. \<exists>f. isFork [] f \<and> closedFork f [] \<and> t = margin f []}"
    by blast 
  then have zero_in: "ss = {0}"
    by (smt Collect_cong ListOfAdverse.Nil closedFork_ListOfAdverse isFork_Nil margin_no_honest margin_of_nil_aux root_label_0.cases singleton_conv)
  then have "Max ss = 0"
    by simp
  have "Max {i. \<exists>n. isFork [] n \<and> closedFork n [] \<and> i = margin n []} = 0"
      using \<open>Max ss = 0\<close> ss by blast      
  then show ?thesis using margin_of_string_def
    by presburger 
qed      
  
definition m :: "bool list \<Rightarrow> (int, int) prod" where
  "m w = (lambda_of_string w, margin_of_string w)"
    
lemma lemma_4_18_trivial_case_m : "m [] = (0,0)"
  by (simp add: lambda_of_nil m_def margin_of_nil)

lemma lemma_4_18_trivial_case_exist_Fork : 
"\<exists> F. (isFork [] F \<and> closedFork F []  \<and> (m [] = (lambda F [], margin F [])))"
  by (metis ListOfAdverse.Nil closedFork_ListOfAdverse isFork_Nil lambda_of_nil_aux                  
lemma_4_18_trivial_case_m margin_no_honest margin_of_nil_aux root_label_0.cases)
  
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