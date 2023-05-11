chapter \<open>Parity Games\<close>
theory ParityGames
imports Main
begin
section \<open>Parity Game Definitions\<close>
subsection \<open>Directed Graphs\<close>
text \<open>
  An arena \<A> in parity games consists of a directed graph and sets of vertices with owners.
  It is defined as \<A> = (V,V0,V1,E) where
  - (V,E) is a directed graph
  - V0 and V1 = V\V0 are sets of vertices belonging to the two players
  - E \<subseteq> V \<times> V is a set of edges, such that every vertex has at least one successor
  The simplest way for us to represent this is as a directed graph of integers (which will be priorities),
  and a set of vertices belonging to player 0.
\<close>
text \<open>A directed graph is represented as a set of edges\<close>
type_synonym 'v dgraph = "('v\<times>'v) set"
definition succs :: "'v dgraph \<Rightarrow> 'v \<Rightarrow> 'v set" where
  "succs E v \<equiv> E``{v}"
definition is_succ :: "'v dgraph \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "is_succ E v w \<equiv> w \<in> succs E v"

lemma "w \<in> succs E v \<Longrightarrow> is_succ E v w"
  unfolding is_succ_def succs_def by auto

subsection \<open>Paths and Cycles\<close>
context
  fixes E :: "'v dgraph"
begin
  (*definition V where "V = fst`E \<union> snd`E"

  lemma "finite E \<Longrightarrow> finite V"
    unfolding V_def by simp
  *)

  (** A path consisting of the edges of a graph *)
  fun epath :: "'v \<Rightarrow> ('v\<times>'v) list \<Rightarrow> 'v \<Rightarrow> bool" where
    "epath v [] v' \<longleftrightarrow> v=v'"
  | "epath v ((x,y)#es) v' \<longleftrightarrow> x=v \<and> (x,y)\<in>E \<and> epath y es v'"

  (** A path consisting of the second node of each edge of a graph *)
  fun path :: "'v \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> bool" where
     "path v [] v' \<longleftrightarrow> v = v'"
  |  "path v (x#xs) v' \<longleftrightarrow> (v,x) \<in> E \<and> path x xs v'"

  (** Quick check whether the path definition does in fact hold the second node of each edge *)
  lemma "path v vs v' \<Longrightarrow> vs \<noteq> [] \<Longrightarrow> v' \<in> set vs"
    apply (induction vs arbitrary: v) by fastforce+

  (** A path consisting of the first node of each edge of a graph  *)
  fun path' :: "'v \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> bool" where
     "path' v [] v' \<longleftrightarrow> v = v'"
  |  "path' v (x#xs) v' \<longleftrightarrow> (\<exists>y. x=v \<and> (v,y) \<in> E \<and> path' y xs v')"

  lemma
    "path' v [] v' \<longleftrightarrow> v = v'"
    "path' v [x] v' \<longleftrightarrow> v = x \<and> (x,v') \<in> E"
    "path' v (x#(x'#xs)) v' \<longleftrightarrow> v = x \<and> (x,x') \<in> E \<and> path' x'(x'#xs) v'"
    by auto

  (** These lemmas show that the two path definitions are alternative definitions for the edge paths *)
  lemma path_alt: "path u xs v \<longleftrightarrow> (\<exists>es. epath u es v \<and> xs=map snd es)"
    apply (induction xs arbitrary: u)
    subgoal by auto
    subgoal for a xs u apply auto
      by (metis epath.simps(2) list.simps(9) snd_conv)
    done

  lemma path'_alt: "path' u xs v \<longleftrightarrow> (\<exists>es. epath u es v \<and> xs=map fst es)"
    apply (induction u xs v rule: path'.induct)
    apply (auto simp: Cons_eq_map_conv)
    using epath.simps(2) by blast+

  (** These lemmas show that the paths can be composed by appending multiple paths *)
  lemma epath_append[simp]: "epath u (es\<^sub>1@es\<^sub>2) v \<longleftrightarrow> (\<exists>u'. epath u es\<^sub>1 u' \<and> epath u' es\<^sub>2 v)"
    apply (induction es\<^sub>1 arbitrary: u) by auto

  lemma path_append[simp]: "path u (xs\<^sub>1@xs\<^sub>2) v \<longleftrightarrow> (\<exists>u'. path u xs\<^sub>1 u' \<and> path u' xs\<^sub>2 v)"
    apply (induction xs\<^sub>1 arbitrary: u) by auto

  lemma path'_append[simp]: "path' u (xs\<^sub>1@xs\<^sub>2) v \<longleftrightarrow> (\<exists>u'. path' u xs\<^sub>1 u' \<and> path' u' xs\<^sub>2 v)"
    apply (induction xs\<^sub>1 arbitrary: u) by auto

  (** These lemmas show that paths can be decomposed in various ways *)
  lemma path_decomp_1: "path u (xs@[v]@ys) w \<Longrightarrow> path u (xs@[v]) v" by auto

  lemma path_decomp_2: "path u (xs@[v]@ys@[w]@zs) x \<Longrightarrow> path v (ys@[w]) w" by auto

  lemma path'_decomp_1: "path' u (xs@[v]@ys) w \<Longrightarrow> path' u (xs) v" by auto

  lemma path'_decomp_2: "path' u (xs@[v]@ys@[w]@zs) x \<Longrightarrow> path' v (v#ys) w" by auto

  (** These lemmas show that paths are equivalent to the reflexive transitive closure *)
  lemma epath_is_rtrancl: "epath v es v' \<Longrightarrow> (v,v')\<in>E\<^sup>*"
  proof (induction es v' rule: epath.induct)
    case (1 v v') thus ?case by simp
  next
    case (2 v x y es v')
    hence "(v,y) \<in> E" by auto
    with 2 show ?case by simp
  qed

  lemma rtrancl_is_epath: "(v,v')\<in>E\<^sup>* \<Longrightarrow> \<exists>es. epath v es v'"
    apply (induction rule: converse_rtrancl_induct)
    using epath.simps(1) epath.simps(2) by blast+

  lemma epath_equiv_rtrancl: "(u,v)\<in>E\<^sup>* \<longleftrightarrow> (\<exists>es. epath u es v)"
    apply auto by (simp add: rtrancl_is_epath epath_is_rtrancl)+

  lemma path_is_rtrancl: "path v xs v' \<Longrightarrow> (v,v')\<in>E\<^sup>*"
    apply (induction xs arbitrary: v) by fastforce+

  lemma rtrancl_is_path: "(v,v')\<in>E\<^sup>* \<Longrightarrow> \<exists>xs. path v xs v'"
    apply (induction rule: converse_rtrancl_induct)
    using path.simps(1) path.simps(2) by blast+

  lemma path_equiv_rtrancl: "(v,v') \<in> E\<^sup>* \<longleftrightarrow> (\<exists>xs. path v xs v')"
    apply auto by (simp add: rtrancl_is_path path_is_rtrancl)+

  lemma path'_is_rtrancl: "path' v xs v' \<Longrightarrow> (v,v')\<in>E\<^sup>*"
    apply (induction xs arbitrary: v) by fastforce+

  lemma rtrancl_is_path': "(v,v')\<in>E\<^sup>* \<Longrightarrow> \<exists>xs. path' v xs v'"
    apply (induction rule: converse_rtrancl_induct)
    using path'.simps(1) path'.simps(2) by blast+

  lemma path'_equiv_rtrancl: "(v,v') \<in> E\<^sup>* \<longleftrightarrow> (\<exists>xs. path' v xs v')"
    apply auto by (simp add: rtrancl_is_path' path'_is_rtrancl)+

  (** These lemmas show that paths are a subset of the graph *)
  lemma epath_subset: "epath v es v' \<Longrightarrow> set es \<subseteq> E"
    using split_list by fastforce

  lemma path_subset: "path v xs v' \<Longrightarrow> set xs \<subseteq> fst`E \<union> snd`E"
  proof (induction xs arbitrary: v)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    hence "(v,a) \<in> E" by simp
    hence "a \<in> snd ` E" by force
    with Cons show ?case by auto
  qed

  lemma path'_subset: "path' v xs v' \<Longrightarrow> set xs \<subseteq> fst`E \<union> snd`E"
  proof (induction xs arbitrary: v)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    hence "v = a" by auto
    moreover from this Cons have "\<exists>y. (v,y)\<in>E" by auto
    ultimately have "a \<in> fst ` E" by force
    with Cons show ?case by auto
  qed

  lemma path_equiv_path': "path v (xs@[v']) v' \<Longrightarrow> path' v (v#xs) v'"
    apply (induction xs arbitrary: v) by auto

  lemma path'_equiv_path: "path' v (v#xs) v' \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> path v (xs@[v']) v'"
    apply (induction xs arbitrary: v) by fastforce+

  lemma origin_in_path':  "path' v vs v' \<and> vs \<noteq> [] \<Longrightarrow> v \<in> set vs" by (cases vs) auto

  lemma path'D: "path' v vs v' \<and> vs \<noteq> [] \<Longrightarrow> \<exists>y vs'. vs = v#(vs') \<and> (v,y) \<in> E \<and> path' y vs' v'"
    apply (induction vs arbitrary: v) by simp+

  lemma path'_loop: "path' v (x#y#ys) v \<Longrightarrow> path' y (y#ys@[v]) y"
    by (induction ys arbitrary: v; simp)

  lemma distinct_length: "distinct xs \<Longrightarrow> length xs = card (set xs)"
    apply (induction xs) by auto

  lemma not_distinct_length: "length xs > card (set xs) \<Longrightarrow> \<not>distinct xs"
    apply (induction xs) by auto

  lemma finite_subset_not_distinct: "finite S \<Longrightarrow> set xs \<subseteq> S \<Longrightarrow> length xs > card S \<Longrightarrow> \<not>distinct xs"
  proof (rule ccontr; simp)
    assume finite: "finite S"
      and subset: "set xs \<subseteq> S"
      and len: "length xs > card S"
      and distinct: "distinct xs"
    hence "card (set xs) = length xs" by (simp add: distinct_length)
    with len have card_gt: "card (set xs) > card S" by simp
    also from subset finite have card_lt_eq: "card (set xs) \<le> card S"
      using card_mono by blast
    finally show "False" by auto
  qed

  definition cycle_node :: "'v \<Rightarrow> 'v list \<Rightarrow> bool" where
    "cycle_node v xs \<equiv> path' v xs v \<and> xs \<noteq> []"

  lemma cycle_node_not_empty[simp]:"\<not>cycle_node v []"
    unfolding cycle_node_def by auto

  definition cycle_from_node :: "'v \<Rightarrow> 'v list \<Rightarrow> bool" where
    "cycle_from_node v xs \<equiv> \<exists>v'. (v,v')\<in>E\<^sup>* \<and> cycle_node v' xs"

  lemma cycle_from_node_not_empty[simp]: "\<not>cycle_from_node v []"
    unfolding cycle_from_node_def by auto

  lemma cycle_from_node_comp: "path' u xs v \<Longrightarrow> cycle_node v ys \<Longrightarrow> cycle_from_node u ys"
    unfolding cycle_from_node_def using path'_is_rtrancl by blast

  lemma cycle_from_node_decomp: "cycle_from_node u ys \<Longrightarrow> \<exists>xs v. cycle_node v ys \<and> path' u xs v"
    unfolding cycle_from_node_def using rtrancl_is_path' by blast

  definition lasso_from_node :: "'v \<Rightarrow> 'v list \<Rightarrow> 'v list \<Rightarrow> bool" where
    "lasso_from_node v xs ys \<equiv> \<exists>v'. path' v xs v' \<and> path' v' ys v' \<and> ys \<noteq> []"

  lemma lasso_from_node_not_empty[simp]:"\<not>lasso_from_node v xs []"
    unfolding lasso_from_node_def by auto

  lemma origin_in_lasso: "lasso_from_node x xs ys \<Longrightarrow> (x \<in> set xs \<or> x \<in> set ys)"
    unfolding lasso_from_node_def
    apply (induction xs arbitrary: x; simp)
    using origin_in_path' by auto

  definition lasso_from_node' :: "'v \<Rightarrow> 'v list \<Rightarrow> bool" where
    "lasso_from_node' v xs \<equiv> \<exists>v' xs1 xs2. xs=xs1@xs2 \<and>  path' v xs1 v' \<and> path' v' xs2 v' \<and> xs2 \<noteq> []"

  lemma lasso_from_node'_not_empty[simp]: "\<not>lasso_from_node' v []"
    unfolding lasso_from_node'_def by auto

  lemma cycle_impl_lasso': "cycle_node v xs \<Longrightarrow> lasso_from_node' v xs"
    unfolding cycle_node_def lasso_from_node'_def by fastforce

  lemma lassos_equiv: "lasso_from_node' v xs \<longleftrightarrow> (\<exists>xs1 xs2. xs=xs1@xs2 \<and> lasso_from_node v xs1 xs2)"
    unfolding lasso_from_node'_def lasso_from_node_def
    apply (induction xs arbitrary: v) by auto

  lemma lasso'_impl_path: "lasso_from_node' v xs \<Longrightarrow> \<exists>v'. path' v xs v'"
    unfolding lasso_from_node'_def by force

  lemma origin_in_lasso': "lasso_from_node' v xs \<Longrightarrow> v \<in> set xs"
    apply (induction xs arbitrary: v; simp)
    using lasso'_impl_path origin_in_path' by fastforce

  lemma lasso'_iff_path: "lasso_from_node' v xs \<longleftrightarrow> (\<exists>v'\<in>set xs. path' v xs v')"
    unfolding lasso_from_node'_def
    apply (auto simp: in_set_conv_decomp neq_Nil_conv) by force

  lemma lasso_from_node'_consD: "lasso_from_node' v (x#xs)
    \<Longrightarrow> (\<exists>v' xs'. x=v \<and> (v,v')\<in>E \<and> lasso_from_node' v' xs' \<and> set xs'\<subseteq>set (x#xs))"
    by (auto simp: lasso_from_node'_def Cons_eq_append_conv; force)

  lemma lasso_from_node'_prepend: "\<lbrakk> lasso_from_node' v' xs; (v,v') \<in> E \<rbrakk> \<Longrightarrow> lasso_from_node' v (v#xs)"
    unfolding lasso_from_node'_def
    apply (induction xs arbitrary: v')
    subgoal by simp
    subgoal for x' xs' by (metis ParityGames.path'.simps(2) append_Cons)
    done

  lemma self_lasso': "\<lbrakk> path' v vs v; vs \<noteq> [] \<rbrakk> \<Longrightarrow> lasso_from_node' v vs"
    unfolding lasso_from_node'_def by force

  lemma lasso'_close_loop: "\<lbrakk> path' v' vs v; vs \<noteq> []; (v,v') \<in> E \<rbrakk> \<Longrightarrow> lasso_from_node' v' (vs@[v])"
    unfolding lasso_from_node'_def by fastforce

  lemma lasso_from_equiv_cycle_from: "cycle_from_node v ys \<longleftrightarrow> (\<exists>xs. lasso_from_node v xs ys)"
    unfolding lasso_from_node_def cycle_from_node_def cycle_node_def
  proof
    assume "\<exists>v'. (v,v') \<in> E\<^sup>* \<and> path' v' ys v' \<and> ys \<noteq> []"
    then show "\<exists>xs v'. local.path' v xs v' \<and> local.path' v' ys v' \<and> ys \<noteq> []"
      using path'_equiv_rtrancl by auto
  next
    assume "\<exists>xs v'. path' v xs v' \<and> path' v' ys v' \<and> ys \<noteq> []"
    then show "\<exists>v'. (v,v') \<in> E\<^sup>* \<and> path' v' ys v' \<and> ys \<noteq> []"
      using path'_is_rtrancl by auto
  qed
end

locale finite_graph_V =
  fixes E :: "'v dgraph"
  fixes V :: "'v set"
  assumes E_in_V: "E \<subseteq> V \<times> V"
  assumes fin_V[simp, intro]: "finite V"
  assumes succ: "v\<in>V \<Longrightarrow> E``{v}\<noteq>{}"
begin
  lemma fin_E[simp, intro!]: "finite E"
    using E_in_V by (simp add: finite_subset)

  lemma path_closed_V: "v\<in>V \<Longrightarrow> path' E v xs v' \<Longrightarrow> v'\<in>V"
    apply (induction xs arbitrary: v)
    using E_in_V
    by auto

  lemma path_any_length: "\<lbrakk>v\<in>V\<rbrakk> \<Longrightarrow> \<exists>xs v'. length xs = n \<and> path' E v xs v'"
  proof (induction n)
    case 0
    then obtain xs v' where "xs=([]::'v list)" and "v' = v" by simp
    then show ?case by auto
  next
    case (Suc n)
    then obtain xs v' where path: "length xs = n" "path' E v xs v'" by auto
    from path_closed_V[OF \<open>v\<in>V\<close> path(2)] Suc succ obtain w where succ: "w \<in> E``{v'}" by blast
    then obtain ys where append: "ys = xs@[v']" by fast
    with path have length: "length ys = Suc n" by simp
    from append path succ have "path' E v ys w" by auto
    with length show ?case by auto
  qed

  lemma finite_graph_always_has_cycle_from_node: "x\<in>V \<Longrightarrow> \<exists>xs. cycle_from_node E x xs"
  proof -
    assume "x\<in>V"
    then obtain xs x' where xs: "length (xs::'v list) = (card V) + 1 \<and> path' E x xs x'"
      using path_any_length by blast
    have "\<not>distinct xs" proof -
      from xs have "set xs \<subseteq> V" using path'_subset E_in_V by fastforce
      moreover from xs have "length xs > card V" by auto
      ultimately show ?thesis using finite_subset_not_distinct by blast
    qed
    hence "\<exists>y xs1 xs2 xs3. xs = xs1 @ [y] @ xs2 @ [y] @ xs3" using not_distinct_decomp by blast
    then obtain y xs1 xs2 xs3 where decomp: "xs = xs1 @ [y] @ xs2 @ [y] @ xs3" by blast
    with xs have "path' E x (xs1) y" by auto
    moreover from decomp xs have "path' E y (y#xs2) y" by auto
    hence "cycle_node E y (y#xs2)" by (simp add: cycle_node_def)
    ultimately have "cycle_from_node E x (y#xs2)" using cycle_from_node_comp by fastforce
    then show "\<exists>xs. cycle_from_node E x xs" by auto
  qed

  lemma finite_graph_always_has_lasso': "x\<in>V \<Longrightarrow> \<exists>xs. lasso_from_node' E x xs"
  proof-
    assume "x\<in>V"
    then obtain xs x' where xs: "length (xs::'v list) = (card V) + 1 \<and> path' E x xs x'"
      using path_any_length by blast
    have "\<not>distinct xs" proof -
      from xs have "set xs \<subseteq> V" using path'_subset E_in_V by fastforce
      moreover from xs have "length xs > card V" by auto
      ultimately show ?thesis using finite_subset_not_distinct by blast
    qed
    hence "\<exists>y xs1 xs2 xs3. xs = xs1 @ [y] @ xs2 @ [y] @ xs3" using not_distinct_decomp by blast
    then obtain y xs1 xs2 xs3 where decomp: "xs = xs1 @ [y] @ xs2 @ [y] @ xs3" by blast
    with xs have "path' E x xs1 y" by auto
    moreover from decomp xs have "path' E y (y#xs2) y" by auto
    ultimately have "lasso_from_node' E x (xs1@(y#xs2))" unfolding lasso_from_node'_def by blast
    then show "\<exists>xs. lasso_from_node' E x xs" by auto
  qed

end

subsection \<open>Paths in Subgraphs\<close>

lemma simulate_path_aux:
  assumes "E``(Y-X) \<subseteq> Y"
  assumes "v\<in>Y"
  assumes "path' E v xs v'"
  shows "X\<inter>set xs \<noteq> {} \<or> (path' (E \<inter> (Y-X)\<times>Y) v xs v')"
  using assms(2,3)
  apply (induction xs arbitrary: v)
  using assms(1)
  by auto

lemma subgraph_path': "E' \<subseteq> E \<Longrightarrow> path' E' v vs v' \<Longrightarrow> path' E v vs v'"
  apply (induction vs arbitrary: v) by auto

lemma subgraph_cycle: "E' \<subseteq> E \<Longrightarrow> cycle_node E' v vs \<Longrightarrow> cycle_node E v vs"
  unfolding cycle_node_def
  apply (induction vs arbitrary: v)
  by (auto simp: subgraph_path')

lemma subgraph_cycle_from_node: "E' \<subseteq> E \<Longrightarrow> cycle_from_node E' v vs \<Longrightarrow> cycle_from_node E v vs"
  unfolding cycle_from_node_def
  proof (induction vs arbitrary: v)
    case Nil
    then show ?case by (simp add: cycle_node_def)
  next
    case (Cons a vs)
    then obtain v' where v_v'_sub: "(v,v')\<in>E'\<^sup>*"
      and cycle_v'_sub: "cycle_node E' v' (a # vs)" by fast
    from v_v'_sub Cons.prems(1) have v_v': "(v,v')\<in>E\<^sup>*"
      using rtrancl_mono by auto
    from cycle_v'_sub Cons.prems(1) have cycle_v': "cycle_node E v' (a # vs)"
      by (auto simp: subgraph_cycle)
    with v_v' show ?case by auto
  qed

lemma subgraph_lasso': "E' \<subseteq> E \<Longrightarrow> lasso_from_node' E' v vs \<Longrightarrow> lasso_from_node' E v vs"
  unfolding lasso_from_node'_def
  apply (induction vs arbitrary: v)
  apply blast by (meson subgraph_path')

lemma cycle_from_node_inter_1: "cycle_from_node (E1 \<inter> E2) v vs \<Longrightarrow> cycle_from_node E1 v vs"
  proof -
    assume "cycle_from_node (E1 \<inter> E2) v vs"
    moreover have "(E1 \<inter> E2) \<subseteq> E1" by fast
    ultimately show "cycle_from_node E1 v vs" using subgraph_cycle_from_node by metis
  qed

lemma cycle_from_node_inter_2: "cycle_from_node (E1 \<inter> E2) v vs \<Longrightarrow> cycle_from_node E2 v vs"
  proof -
    assume "cycle_from_node (E1 \<inter> E2) v vs"
    moreover have "(E1 \<inter> E2) \<subseteq> E2" by fast
    ultimately show "cycle_from_node E2 v vs" using subgraph_cycle_from_node by metis
  qed

subsection \<open>Winning Strategies\<close>

locale arena_defs = finite_graph_V +
  fixes V\<^sub>0 :: "'v set"
  fixes prio :: "'v \<Rightarrow> nat"
  assumes V\<^sub>0_in_V: "V\<^sub>0 \<subseteq> V"
begin
  definition V\<^sub>1 where "V\<^sub>1 = V - V\<^sub>0"

  lemma "V\<^sub>0 = V - V\<^sub>1" using V\<^sub>0_in_V unfolding V\<^sub>1_def by auto

  lemma V_fst_E: "v \<in> V \<longleftrightarrow> v \<in> fst`E"
    apply rule
    subgoal using succ by force
    subgoal using E_in_V by auto
    done

  lemma players_disjoint: "V\<^sub>0 \<inter> V\<^sub>1 = {}"
    unfolding V\<^sub>1_def by auto

  lemma in_V\<^sub>1_notin_V\<^sub>0: "v\<in>V \<Longrightarrow> v\<notin>V\<^sub>0 \<longleftrightarrow> v\<in>V\<^sub>1"
    unfolding V\<^sub>1_def by blast

  text \<open>A positional strategy for a player i is a function \<sigma>:Vi\<rightarrow>V\<close>
  type_synonym 'a strat = "'a \<Rightarrow> 'a option"

  definition E_of_strat :: "'a strat \<Rightarrow> 'a dgraph" where
    "E_of_strat \<sigma> = {(u,v). \<sigma> u = Some v}"

  lemma E_of_strat_empty[simp]: "E_of_strat Map.empty = {}"
    unfolding E_of_strat_def by fast

  lemma E_of_strat_eq_empty_conv[simp]: "E_of_strat \<sigma> = {} \<longleftrightarrow> \<sigma> = Map.empty"
    unfolding E_of_strat_def by auto

  lemma E_of_strat_dom: "dom \<sigma> = fst`E_of_strat \<sigma>"
    unfolding E_of_strat_def by force

  lemma E_of_strat_dom_node: "v \<in> dom \<sigma> \<longleftrightarrow> v \<in> fst`E_of_strat \<sigma>"
    unfolding E_of_strat_def by force

  lemma E_of_strat_ran: "ran \<sigma> = snd`E_of_strat \<sigma>"
    unfolding E_of_strat_def ran_def by force

  lemma E_of_strat_ran_subset[simp]: "ran \<sigma> \<subseteq> X \<Longrightarrow> E_of_strat \<sigma> `` {x} \<subseteq> X"
    unfolding E_of_strat_def by (auto simp: ranI)

  definition top_priority :: "'v list \<Rightarrow> nat" where
    "top_priority xs \<equiv> MAX v \<in> set xs. prio v"

  abbreviation winning_even :: "'v list \<Rightarrow> bool" where
    "winning_even xs \<equiv> even (top_priority xs)"

  abbreviation winning_odd :: "'v list \<Rightarrow> bool" where
    "winning_odd xs \<equiv> odd (top_priority xs)"

  definition strategy_of :: "'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
    "strategy_of S \<sigma> \<equiv> dom \<sigma> \<subseteq> S \<and> E_of_strat \<sigma> \<subseteq> E"

  lemma strategy_of_empty[simp]: "strategy_of S Map.empty"
    unfolding strategy_of_def by auto

  lemma strategy_of_map_assign: "\<lbrakk> x\<in>S; (x,y)\<in>E \<rbrakk> \<Longrightarrow> strategy_of S [x\<mapsto>y]"
    unfolding strategy_of_def E_of_strat_def
    by (auto split: if_splits)

  lemma strategy_of_empty_iff_empty_strategy[simp]: "strategy_of {} \<sigma> \<longleftrightarrow> \<sigma> = Map.empty"
    unfolding strategy_of_def by auto

  lemma strategy_of_add_same[simp]: "\<lbrakk> strategy_of S \<sigma>; strategy_of S \<sigma>' \<rbrakk> \<Longrightarrow> strategy_of S (\<sigma> ++ \<sigma>')"
    unfolding strategy_of_def E_of_strat_def by auto

  lemma strategy_of_dom: "\<lbrakk> strategy_of S \<sigma>; v \<in> dom \<sigma> \<rbrakk> \<Longrightarrow> v \<in> S"
    unfolding strategy_of_def by fast

  lemma strategy_of_add_disj: "S \<inter> S' = {} \<Longrightarrow> strategy_of S \<sigma> \<and> strategy_of S' \<sigma>'
    \<Longrightarrow> dom \<sigma> \<inter> dom \<sigma>' = {}"
    unfolding strategy_of_def by blast

  lemma strategies_disjoint: "strategy_of V\<^sub>0 \<sigma> \<and> strategy_of V\<^sub>1 \<sigma>' \<Longrightarrow> dom \<sigma> \<inter> dom \<sigma>' = {}"
    using strategy_of_add_disj players_disjoint by blast

  definition induced_by_strategy :: "'v set \<Rightarrow> 'v strat \<Rightarrow> 'v dgraph" where
    "induced_by_strategy V\<^sub>\<alpha> \<sigma> = E \<inter> ((-V\<^sub>\<alpha>) \<times> UNIV \<union> E_of_strat \<sigma>)"

  lemma induced_by_strategy_empty[simp]: "induced_by_strategy V\<^sub>\<alpha> Map.empty = E \<inter> (-V\<^sub>\<alpha>) \<times> UNIV"
    unfolding induced_by_strategy_def by simp

  lemma ind_subgraph: "induced_by_strategy V\<^sub>\<alpha> \<sigma> \<subseteq> E"
    unfolding induced_by_strategy_def by auto

  lemma ind_subgraph_not_in_dom: "\<lbrakk> (v,w) \<in> E; v \<notin> V\<^sub>\<alpha> \<rbrakk> \<Longrightarrow> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>"
    unfolding induced_by_strategy_def E_of_strat_def by fast

  lemma ind_subgraph_edge_in_E[simp]: "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<Longrightarrow> (v,w) \<in> E"
    using ind_subgraph by blast

  lemma ind_subgraph_edge_src: "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<Longrightarrow> v \<in> dom \<sigma> \<or> v \<in> (-V\<^sub>\<alpha>)"
    unfolding induced_by_strategy_def E_of_strat_def by auto

  lemma ind_subgraph_edge_dst: "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<Longrightarrow> v \<in> V\<^sub>\<alpha> \<Longrightarrow> w \<in> ran \<sigma>"
    unfolding induced_by_strategy_def E_of_strat_def ran_def by blast

  lemma ind_subgraph_finite[simp]: "finite (induced_by_strategy V\<^sub>\<alpha> \<sigma>)"
    using ind_subgraph fin_E finite_subset by blast

  lemma ind_subgraph_addD: "induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>') \<subseteq> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<union> E_of_strat \<sigma>'"
    unfolding induced_by_strategy_def E_of_strat_def by auto

  lemma ind_subgraph_add_edge: "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>')
    \<Longrightarrow> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<or> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>'"
    unfolding induced_by_strategy_def E_of_strat_def by fast

  lemma ind_subgraph_add_edge_src: "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>')
    \<Longrightarrow> v \<in> dom \<sigma> \<or> v \<in> dom \<sigma>' \<or> v \<in> (-V\<^sub>\<alpha>)"
    unfolding induced_by_strategy_def E_of_strat_def by blast

  lemma ind_subgraph_add_edge_outside_strat: "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>') \<Longrightarrow> v \<in> (-V\<^sub>\<alpha>)
    \<Longrightarrow> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<and> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>'"
    unfolding induced_by_strategy_def E_of_strat_def by fast

  lemma ind_subgraph_add_edge_dom_\<sigma>: "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>') \<Longrightarrow> dom \<sigma> \<inter> dom \<sigma>' = {}
       \<Longrightarrow> v \<in> dom \<sigma> \<Longrightarrow> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>"
      unfolding induced_by_strategy_def E_of_strat_def by auto

  lemma ind_subgraph_add_edge_dom_\<sigma>': "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>') \<Longrightarrow> v \<in> dom \<sigma>'
     \<Longrightarrow> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>'"
    unfolding induced_by_strategy_def E_of_strat_def by blast

  lemma ind_subgraph_to_strategy: "\<lbrakk>(v, w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>; strategy_of V\<^sub>\<alpha> \<sigma>; v \<in> dom \<sigma> \<rbrakk>
    \<Longrightarrow> \<sigma> v = Some w"
    unfolding induced_by_strategy_def strategy_of_def E_of_strat_def by blast

  lemma strategy_to_ind_subgraph: "\<lbrakk>\<sigma> v = Some w; (v,w) \<in> E \<rbrakk> \<Longrightarrow> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>"
    unfolding induced_by_strategy_def E_of_strat_def by auto

  lemma ind_subgraph_add_disjoint_doms: "\<lbrakk> dom \<sigma> \<inter> dom \<sigma>' = {}; strategy_of V\<^sub>\<alpha> \<sigma> \<rbrakk>
    \<Longrightarrow> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<subseteq> induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>')"
  proof -
    assume
      doms_disj: "dom \<sigma> \<inter> dom \<sigma>' = {}" and
      strat_of_\<sigma>:  "strategy_of V\<^sub>\<alpha> \<sigma>"

    let ?\<tau> = "\<sigma> ++ \<sigma>'"

    have "\<forall>v w. (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<longrightarrow> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> ?\<tau>"
    proof (intro allI; rule impI)
      fix v w
      assume in_\<sigma>: "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>"
      hence edge_in_E[simp]: "(v,w) \<in> E" by simp

      from in_\<sigma> consider (own_node) "v \<in> dom \<sigma>" | (opponent_node) "v \<in> -V\<^sub>\<alpha>"
        using ind_subgraph_edge_src by blast
      thus "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> ?\<tau>" proof cases
        case own_node
        with in_\<sigma> strat_of_\<sigma> have "\<sigma> v = Some w"
          using ind_subgraph_to_strategy by auto
        with doms_disj have "?\<tau> v = Some w"
          using map_add_comm by fastforce
        thus ?thesis
          using strategy_to_ind_subgraph by auto
      next
        case opponent_node thus ?thesis
          unfolding induced_by_strategy_def E_of_strat_def by auto
      qed
    qed

    thus ?thesis by force
  qed

  lemma ind_subgraph_add_disjoint_doms': "\<lbrakk> dom \<sigma> \<inter> dom \<sigma>' = {}; strategy_of V\<^sub>\<alpha> \<sigma>; strategy_of V\<^sub>\<alpha> \<sigma>' \<rbrakk>
    \<Longrightarrow> induced_by_strategy V\<^sub>\<alpha> \<sigma> = induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>') - dom \<sigma>' \<times> UNIV"
  proof -
    assume
        doms_disj: "dom \<sigma> \<inter> dom \<sigma>' = {}" and
        strat_of_\<sigma>: "strategy_of V\<^sub>\<alpha> \<sigma>" and
        strat_of_\<sigma>': "strategy_of V\<^sub>\<alpha> \<sigma>'"

    let ?\<tau> = "\<sigma> ++ \<sigma>'"
    from strat_of_\<sigma> strat_of_\<sigma>' have strat_of_\<tau>: "strategy_of V\<^sub>\<alpha> ?\<tau>" by simp

    have "\<forall>v w. (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<longrightarrow> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> ?\<tau> - dom \<sigma>' \<times> UNIV"
    proof (intro allI; rule impI)
      fix v w
      assume in_\<sigma>: "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>"
      hence edge_in_E[simp]: "(v,w) \<in> E" by simp

      from in_\<sigma> consider (own_node) "v \<in> dom \<sigma>" | (opponent_node) "v \<in> -V\<^sub>\<alpha>"
        using ind_subgraph_edge_src by blast
      thus "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> ?\<tau> - dom \<sigma>' \<times> UNIV" proof cases
        case own_node
        with in_\<sigma> strat_of_\<sigma> have "\<sigma> v = Some w"
          using ind_subgraph_to_strategy by auto
        with doms_disj have edge_in_\<sigma>: "?\<tau> v = Some w"
          using map_add_comm by fastforce
        from own_node strat_of_\<sigma>' doms_disj have v_notin_dom_\<sigma>': "v \<notin> dom \<sigma>'"
          using ind_subgraph_edge_src[OF in_\<sigma>] by auto
        from edge_in_\<sigma> v_notin_dom_\<sigma>' show ?thesis
          using strategy_to_ind_subgraph by auto
      next
        case opponent_node
        with strat_of_\<sigma>' have "v \<notin> dom \<sigma>'"
          unfolding strategy_of_def
          using ind_subgraph_edge_src[OF in_\<sigma>]
          by auto
        with opponent_node show ?thesis
          unfolding induced_by_strategy_def E_of_strat_def by auto
      qed
    qed

    moreover have "\<forall>v w. (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> ?\<tau> - dom \<sigma>' \<times> UNIV \<longrightarrow> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>"
    proof (intro allI; rule impI)
      fix v w
      assume in_\<sigma>': "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> ?\<tau> - dom \<sigma>' \<times> UNIV"
      hence edge_in_E[simp]: "(v,w) \<in> E" by force

      from in_\<sigma>' consider (own_node) "v \<in> dom ?\<tau> - dom \<sigma>'" | (opponent_node) "v \<in> -V\<^sub>\<alpha>"
        using ind_subgraph_edge_src by fastforce
      thus "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>" proof cases
        case own_node
        with in_\<sigma>' strat_of_\<tau> have "?\<tau> v = Some w"
          using ind_subgraph_to_strategy by fastforce
        with own_node doms_disj have "\<sigma> v = Some w"
          using map_add_comm by blast
        thus ?thesis using strategy_to_ind_subgraph by force
      next
        case opponent_node thus ?thesis
          unfolding induced_by_strategy_def E_of_strat_def by auto
      qed
    qed

    ultimately show ?thesis by fast
  qed

  lemma ind_subgraph_cycle: "cycle_node (induced_by_strategy V\<^sub>\<alpha> \<sigma>) v xs \<Longrightarrow> cycle_node E v xs"
    using subgraph_cycle by (metis ind_subgraph)

  lemma ind_subgraph_cycle_from_node: "cycle_from_node (induced_by_strategy V\<^sub>\<alpha> \<sigma>) v xs
     \<Longrightarrow> cycle_from_node E v xs"
    using subgraph_cycle_from_node by (metis ind_subgraph)

  lemma ind_subgraph_lasso': "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) v xs
    \<Longrightarrow> lasso_from_node' E v xs"
    using subgraph_lasso' by (metis ind_subgraph)

end


locale player_arena = arena_defs E V V\<^sub>0 prio
  for E V and V\<^sub>0 :: "'v set" and prio
 +
  fixes V\<^sub>\<alpha> :: "'v set"
  fixes winningP :: "nat \<Rightarrow> bool"
  assumes V\<^sub>\<alpha>_subset: "V\<^sub>\<alpha> \<subseteq> V"

  (* assumes "V\<^sub>\<alpha> = V\<^sub>0 \<or> V\<^sub>\<alpha> = V-V\<^sub>0" *)
begin
  abbreviation (input) owned_target :: "'v set \<Rightarrow> 'v set" where
    "owned_target Y \<equiv> {v|v. v\<in>V\<^sub>\<alpha> \<and> E``{v} \<inter> Y \<noteq> {}}"

  abbreviation (input) opponent_target :: "'v set \<Rightarrow> 'v set" where
    "opponent_target Y \<equiv> {v|v. v\<in>-V\<^sub>\<alpha> \<and> E``{v} \<subseteq> Y}"

  inductive is_attractor :: "'v set \<Rightarrow> 'v set \<Rightarrow> bool" for X where
    base: "is_attractor X X" |
    step: "is_attractor X Y \<Longrightarrow> Y' = Y \<union> owned_target Y \<union> opponent_target Y \<Longrightarrow>  is_attractor X Y'"

  inductive_set attractor :: "'v set \<Rightarrow> 'v set" for X where
    base: "x \<in> X \<Longrightarrow> x \<in> attractor X"
  | own: "\<lbrakk> x \<in> V\<^sub>\<alpha>-X; (x,y)\<in>E; y\<in>attractor X \<rbrakk> \<Longrightarrow> x \<in> attractor X"
  | opponent: "\<lbrakk> x\<in>V-V\<^sub>\<alpha>-X; \<forall>y. (x,y)\<in>E \<longrightarrow> y\<in>attractor X \<rbrakk> \<Longrightarrow> x \<in> attractor X"

  lemma attractor_subset: "X \<subseteq> attractor X"
    by (auto intro: base)

  inductive_set attractor_edges :: "'v set \<Rightarrow> ('v \<times> 'v) set" for X where
    ae_base: "x \<in> X \<Longrightarrow> (x,x) \<in> attractor_edges X"
  | ae_own: "\<lbrakk> x \<in> V\<^sub>\<alpha>; (x,y)\<in>E; (y,y_tgt)\<in>attractor_edges X \<rbrakk> \<Longrightarrow> (x,y) \<in> attractor_edges X"
  | ae_opponent: "\<lbrakk> x\<in>V-V\<^sub>\<alpha>; \<forall>y. (x,y)\<in>E \<longrightarrow> (\<exists>y_tgt. (y,y_tgt)\<in>attractor_edges X) \<rbrakk> \<Longrightarrow> (x,x) \<in> attractor_edges X"

  lemma attractor_edges_sound: "(x,y)\<in>attractor_edges X \<Longrightarrow> x\<in>attractor X"
    apply (induction rule: attractor_edges.induct)
    by (auto intro: base own opponent)

  lemma attractor_edges_complete: "x\<in>attractor X \<Longrightarrow> (\<exists>y. (x,y)\<in>attractor_edges X)"
    apply (induction rule: attractor.induct)
    by (auto 0 3 intro: ae_base ae_own ae_opponent)

  lemma attractor_edges_edges: "(x,y)\<in>attractor_edges X \<Longrightarrow> x\<in>V\<^sub>\<alpha>-X \<Longrightarrow>(x,y)\<in>E"
    apply (induction rule: attractor_edges.induct)
    by (auto intro: base own opponent)

  definition "attractor_strategy X v \<equiv>
    if v\<notin>X \<and> v\<in>V\<^sub>\<alpha> \<and> (\<exists>v'. (v,v')\<in>attractor_edges X) then
      Some (SOME v'. (v,v')\<in>attractor_edges X)
    else
      None
      "

  lemma attractor_strategy_edges: "attractor_strategy X v = Some v' \<Longrightarrow> (v,v') \<in> attractor_edges X"
    unfolding attractor_strategy_def
    by (auto split: if_splits dest!: sym[of _ v'] intro: someI)

  lemma attractor_strategy_edges_E: "attractor_strategy X v = Some v' \<Longrightarrow> (v,v') \<in> E"
  proof -
    assume assm: "attractor_strategy X v = Some v'"
    from assm have A: "(v,v') \<in> attractor_edges X" using attractor_strategy_edges by auto
    from assm have B: "v\<in>V\<^sub>\<alpha>-X" by (auto simp: attractor_strategy_def split: if_splits)
    from attractor_edges_edges[OF A B] show "(v,v') \<in> E" .
  qed

  lemma attractor_strategy_sound: "attractor_strategy X v = Some v' \<Longrightarrow> v \<in> attractor X"
  proof -
    assume assm: "attractor_strategy X v = Some v'"
    hence "(v,v') \<in> attractor_edges X" using attractor_strategy_edges by auto
    from attractor_edges_sound[OF this] show ?thesis .
  qed

  lemma "attractor_strategy X v = Some v' \<Longrightarrow> v' \<in> attractor X"
    apply (auto simp: attractor_strategy_def split: if_splits)
    by (metis attractor_edges.simps attractor_edges_sound someI)

  lemma dom_attractor_strategy: "dom (attractor_strategy X) = V\<^sub>\<alpha> \<inter> (attractor X - X)"
    by (auto simp: attractor_strategy_def split: if_splits intro: attractor_edges_sound attractor_edges_complete)

  lemma attractor_strategy_of_V\<^sub>\<alpha>: "strategy_of V\<^sub>\<alpha> (attractor_strategy X)"
    unfolding attractor_strategy_def strategy_of_def E_of_strat_def
    apply (auto split: if_splits)
    using attractor_edges_edges tfl_some by auto

  lemma attractor_strategy_closed_edge: "(x,y) \<in> induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X) \<Longrightarrow> x \<in> attractor X - X
    \<Longrightarrow> y \<in> attractor X"
    unfolding induced_by_strategy_def E_of_strat_def attractor_strategy_def
    using attractor.cases apply (auto split: if_splits)
    by (metis attractor_edges.simps attractor_edges_sound someI)

  lemma attractor_strategy_closed: "induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X) `` (attractor X - X) \<subseteq> attractor X"
    using attractor_strategy_closed_edge by blast

  lemma attractor_strategy_escape_via_X: "(x,y) \<in> induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)
     \<Longrightarrow> x \<in> attractor X \<Longrightarrow> y \<notin> attractor X \<Longrightarrow> x \<in> X"
  proof (rule ccontr)
    assume assms: "(x,y) \<in> induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)"
                  "x \<in> attractor X"
                  "y \<notin> attractor X"
                  "x\<notin>X"
    then show False proof (cases "x\<in>X")
      case True with assms(4) show ?thesis ..
    next
      case False
      with assms(2) have "x\<in>attractor X - X" by blast
      from attractor_strategy_closed_edge[OF assms(1) this] have "y \<in> attractor X" .
      with assms(3) show ?thesis ..
    qed
  qed

  inductive attractor'p :: "'v set \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> bool" for X where
    base: "\<lbrakk> x \<in> X \<rbrakk> \<Longrightarrow> attractor'p X 0 x"
  | own: "\<lbrakk> x \<in> V\<^sub>\<alpha>-X; (x,y)\<in>E; attractor'p X i y \<rbrakk> \<Longrightarrow> attractor'p X (Suc i) x"
  | opponent: "\<lbrakk> x\<in>V-V\<^sub>\<alpha>-X; \<forall>y. (x,y)\<in>E \<longrightarrow> attractor'p X i y \<rbrakk> \<Longrightarrow> attractor'p X (Suc i) x"

  definition "attractor' X i \<equiv> Collect (attractor'p X i)"

  print_statement attractor'p.induct[of _ i x]

  lemma attractor'_induct[consumes 1, case_names base own opponent]:
    assumes "x\<in>attractor' X i"
      and "\<And>x. x \<in> X \<Longrightarrow> P 0 x"
      and "\<And>x y i. \<lbrakk>x \<in> V\<^sub>\<alpha> - X; (x, y) \<in> E; y\<in>attractor' X i; P i y\<rbrakk> \<Longrightarrow> P (Suc i) x"
      and "\<And>x i. \<lbrakk>x \<in> V - V\<^sub>\<alpha> - X; \<forall>y. (x, y) \<in> E \<longrightarrow> y\<in>attractor' X i \<and> P i y\<rbrakk> \<Longrightarrow> P (Suc i) x"
    shows "P i x"
    using attractor'p.induct[of _ i x P] assms
    unfolding attractor'_def
    by auto

  context
    fixes X :: "'v set"
  begin
    fun nodes_in_rank :: "nat \<Rightarrow> 'v set" where
      "nodes_in_rank 0 = X"
    | "nodes_in_rank (Suc n) =
        nodes_in_rank n
      \<union> { x | x y :: 'v. x\<in>V\<^sub>\<alpha> \<and> (x,y)\<in>E \<and> y\<in>nodes_in_rank n }
      \<union> { x. x\<in>V-V\<^sub>\<alpha> \<and> (\<forall>y. (x,y)\<in>E \<longrightarrow> y\<in>nodes_in_rank n)  }
        "

    lemma nodes_in_rank_mono: "n\<le>m \<Longrightarrow> nodes_in_rank n \<subseteq> nodes_in_rank m"
      apply (induction m)
      by (auto simp: le_Suc_eq)

    lemma nodes_in_rank_increasing: "nodes_in_rank (n-Suc 0) \<subseteq> nodes_in_rank n"
      apply (cases n)
      by auto

    lemma nodes_in_rank_ss_attractor: "x\<in>nodes_in_rank n \<Longrightarrow> x\<in>attractor X"
      apply (induction n arbitrary: x)
      by (auto intro: attractor.intros)

    lemma attractor_ss_nodes_in_rank: "x\<in>attractor X \<Longrightarrow> (\<exists>n. x\<in>nodes_in_rank n)"
    proof (induction rule: attractor.induct)
      case (base x)
      then show ?case by (auto intro: exI[where x=0])
    next
      case (own x y)
      then show ?case
        apply clarsimp
        subgoal for n by (auto intro!: exI[where x="Suc n"])
        done
    next
      case (opponent x)
      define n_of_y where "n_of_y \<equiv> \<lambda>y. SOME n. y \<in> nodes_in_rank n"
      define n_max where "n_max \<equiv> MAX y\<in>E``{x}. n_of_y y"

      have "n_of_y ` E `` {x} \<noteq> {}" using opponent.hyps succ by auto
      have FIN: "finite (n_of_y ` E `` {x})" by auto

      have n_of_y: "(x,y)\<in>E \<Longrightarrow> y\<in>nodes_in_rank (n_of_y y)" for y
        unfolding n_of_y_def
        using opponent.IH
        by (auto intro: someI)

      have "(x,y)\<in>E \<Longrightarrow> (\<exists>i\<le>n_max. y\<in>nodes_in_rank i)" for y
        using Max_ge[OF FIN] n_of_y unfolding n_max_def
        by blast
      hence "(x,y)\<in>E \<Longrightarrow> y\<in>nodes_in_rank n_max" for y
        using nodes_in_rank_mono by auto
      then show ?case
        apply (rule_tac exI[where x="Suc n_max"])
        using opponent.hyps
        by simp
    qed

    lemma attractor_eq_nodes_in_rank: "attractor X = \<Union>(nodes_in_rank`UNIV)"
      using attractor_ss_nodes_in_rank nodes_in_rank_ss_attractor by auto

  lemma nodes_in_rank_edges_lower: "\<lbrakk>x' \<in> nodes_in_rank n'; x' \<notin> X; (x', y') \<in> E; x' \<notin> V\<^sub>\<alpha>\<rbrakk> \<Longrightarrow> y' \<in> nodes_in_rank n'"
    apply (induction n') by auto

  (*  \<and> (\<forall>x' \<in> nodes_in_rank n - X. (\<forall>y \<in> (induced_by_strategy V\<^sub>\<alpha> \<sigma>) `` {x'}. y \<in> nodes_in_rank (n-1))) *)
  lemma nodes_in_rank_forces_X: "x\<in>nodes_in_rank n \<Longrightarrow> \<exists>\<sigma>.
         strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> \<subseteq> nodes_in_rank n - X
         \<and> (\<forall>n'. \<forall>x' \<in> nodes_in_rank n' - X. (\<forall>y' \<in> (induced_by_strategy V\<^sub>\<alpha> \<sigma>) `` {x'}. y' \<in> nodes_in_rank (n')))
         \<and> (\<forall>xs z. path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) x xs z \<and> n<length xs \<longrightarrow> set xs \<inter> X \<noteq> {})"
  proof (induction n arbitrary: x)
    case 0
    then show ?case
      apply (rule_tac exI[where x=Map.empty])
      apply (intro conjI)
      subgoal by auto
      subgoal by auto
      subgoal using nodes_in_rank_edges_lower by auto
      subgoal by (auto simp: neq_Nil_conv)
      done

  (* using E_in_V apply (auto simp: neq_Nil_conv) *)
  next
    case (Suc n)

    from Suc.prems consider
      (already_in) "x\<in>nodes_in_rank n"
      | (our_node) y where "x\<notin>nodes_in_rank n" "x\<in>V\<^sub>\<alpha>" "(x,y)\<in>E" "y\<in>nodes_in_rank n"
      | (opponent_node) "x\<notin>nodes_in_rank n" "x\<in>V-V\<^sub>\<alpha>" "\<forall>y\<in>E``{x}. y\<in>nodes_in_rank n"
      by auto
    then show ?case proof cases
      case already_in thus ?thesis
        using Suc.IH[of x] nodes_in_rank_increasing ind_subgraph_edge_src
        apply (clarsimp)
        apply (rule exI)
        by fastforce
    next
      case our_node
      hence "x \<notin> X"
        using nodes_in_rank.simps(1) nodes_in_rank_mono by blast

      from Suc.IH[OF \<open>y\<in>nodes_in_rank n\<close>] obtain \<sigma> where
        strat_\<sigma>: "strategy_of V\<^sub>\<alpha> \<sigma>" and
        dom_\<sigma>: "dom \<sigma> \<subseteq> nodes_in_rank n - X" and
        closed_\<sigma>: "(\<forall>n'. \<forall>x' \<in> nodes_in_rank n' - X. (\<forall>y' \<in> (induced_by_strategy V\<^sub>\<alpha> \<sigma>) `` {x'}. y' \<in> nodes_in_rank (n')))" and
        forces_\<sigma>: "(\<forall>xs z. path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs z \<and> n < length xs \<longrightarrow> set xs \<inter> X \<noteq> {})"
        by blast

      define \<sigma>' where "\<sigma>' = \<sigma> ++ [x\<mapsto>y]"
      from strategy_of_map_assign[OF our_node(2) our_node(3)]
      have strat_assign_x_y: "strategy_of V\<^sub>\<alpha> [x\<mapsto>y]" .
      from strategy_of_add_same[OF strat_\<sigma> this] \<sigma>'_def
      have strat_\<sigma>': "strategy_of V\<^sub>\<alpha> \<sigma>'" by simp

      from our_node dom_\<sigma> have "x \<notin> dom \<sigma>" by blast
      hence doms_disj: "dom \<sigma> \<inter> dom [x\<mapsto>y] = {}" by simp
      from ind_subgraph_add_disjoint_doms'[OF doms_disj strat_\<sigma> strat_assign_x_y]
      have \<sigma>_subgraph_\<sigma>':  "induced_by_strategy V\<^sub>\<alpha> \<sigma> = induced_by_strategy V\<^sub>\<alpha> \<sigma>' - {x} \<times> UNIV"
        using \<sigma>'_def by simp
      hence no_x_edges_in_\<sigma>: "induced_by_strategy V\<^sub>\<alpha> \<sigma> \<inter> {x} \<times> UNIV = {}" by auto
      have "induced_by_strategy V\<^sub>\<alpha> \<sigma> \<subseteq> induced_by_strategy V\<^sub>\<alpha> \<sigma>'" using \<sigma>_subgraph_\<sigma>' by simp

      have "x\<in>V" using V\<^sub>\<alpha>_subset our_node(2) by auto

      have dom_\<sigma>': "dom \<sigma>' \<subseteq> nodes_in_rank (Suc n) - X"
        unfolding \<sigma>'_def
        using \<open>x\<in>V\<close> our_node dom_\<sigma> apply simp
        using nodes_in_rank.simps(1) nodes_in_rank_mono our_node(1) by blast

      have closed_\<sigma>': "(\<forall>n'. \<forall>x' \<in> nodes_in_rank n' - X. (\<forall>y' \<in> (induced_by_strategy V\<^sub>\<alpha> \<sigma>') `` {x'}. y' \<in> nodes_in_rank (n')))"
        using closed_\<sigma> our_node(1,4) nodes_in_rank_mono
        unfolding \<sigma>'_def induced_by_strategy_def E_of_strat_def
        apply (safe; simp split: if_splits)
        by (meson in_mono linorder_linear)

      {
        fix xs z
        assume PATH_XS: "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>') x xs z"
          and LEN_XS: "Suc n < length xs"
        have "x\<notin>dom \<sigma>" using dom_\<sigma> our_node(1) by blast
        then have "(x,yy)\<in>induced_by_strategy V\<^sub>\<alpha> \<sigma>' \<Longrightarrow> yy=y" for yy
          using \<open>x\<in>V\<^sub>\<alpha>\<close> by (auto simp: induced_by_strategy_def E_of_strat_def \<sigma>'_def)

        then obtain xs' where xs': "xs=x#xs'" "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>') y xs' z"
          using PATH_XS LEN_XS
          apply (cases xs)
          by auto

        from our_node(4) xs'(2)
        have "X \<inter> set xs' \<noteq> {} \<or> path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs' z"
        proof (induction xs' arbitrary: y)
          case Nil thus ?case by fastforce
        next
          case (Cons a xs')
          from Cons(3) have a_is_y[simp]: "a=y" by simp
          with Cons obtain y' where y'_edge: "(y,y') \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>'"
            and y'_path_\<sigma>': "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>')  y' xs' z" by auto

          from Cons(2) consider (y_in_X)"y \<in> X" | (y_notin_X) "y \<in> nodes_in_rank n - X" by blast
          thus ?case proof cases
            case y_in_X thus ?thesis by simp
          next
            case y_notin_X
            with y'_edge closed_\<sigma>' have "y' \<in> nodes_in_rank n" by blast
            from Cons.IH[OF this y'_path_\<sigma>'] have y'_path_\<sigma>:
              "X \<inter> set xs' \<noteq> {} \<or> path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y' xs' z" .

            from y'_edge consider "y = x" | "y \<in> dom \<sigma>" | "y \<in> -V\<^sub>\<alpha>"
              using \<sigma>'_def ind_subgraph_edge_src by fastforce
            then have "(y,y') \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>"
              using y'_edge unfolding \<sigma>'_def
              apply cases
              subgoal using Cons.prems(1) our_node(1) by auto
              subgoal using doms_disj ind_subgraph_add_edge_dom_\<sigma> by blast
              subgoal using ind_subgraph_add_edge_outside_strat by blast
              done

            with y'_path_\<sigma> show ?thesis by auto
          qed
        qed

        with xs'(1) have PATH_XS': "set xs \<inter> X \<noteq> {} \<or> path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs' z"
          by auto
        from LEN_XS xs'(1) have LEN_XS': "n < length xs'" by auto
        from xs'(1) PATH_XS' LEN_XS' forces_\<sigma> have "set xs \<inter> X \<noteq> {}" by auto
      } note forces_\<sigma>' = this

      show ?thesis
        apply (rule exI[where x=\<sigma>'])
        using strat_\<sigma>' dom_\<sigma>' closed_\<sigma>' forces_\<sigma>' by blast

    next
      case opponent_node
      from Suc.IH opponent_node(3) have "\<forall>y \<in> E `` {x}. \<exists>\<sigma>.
            strategy_of V\<^sub>\<alpha> \<sigma> \<and>  dom \<sigma> \<subseteq> nodes_in_rank n - X \<and>
            (\<forall>n'. \<forall>x'\<in>nodes_in_rank n' - X. \<forall>y'\<in>induced_by_strategy V\<^sub>\<alpha> \<sigma> `` {x'}. y' \<in> nodes_in_rank n') \<and>
            (\<forall>xs z. path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs z \<and> n < length xs \<longrightarrow> set xs \<inter> X \<noteq> {})"
        by blast

  (* I would have to find one strategy that forces the play to X from all y, but all I know is
             that for each y, there exists a separate strategy to force the play to X *)
      show ?thesis sorry
    qed
  qed
  end
end


context player_arena begin

  abbreviation "winning_player xs \<equiv> winningP (top_priority xs)"
  abbreviation "winning_opponent xs \<equiv> \<not>winningP (top_priority xs)"

  definition won_by_player :: "'v \<Rightarrow> bool" where
    "won_by_player v \<equiv> v\<in>V \<and> (\<exists>\<sigma>. strategy_of V\<^sub>\<alpha> \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy (dom \<sigma>) \<sigma>) v xs \<longrightarrow> winning_player xs))"

  lemma "won_by_player v \<Longrightarrow> (\<exists>\<sigma>. strategy_of V\<^sub>\<alpha> \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy (dom \<sigma>) \<sigma>) v xs \<longrightarrow> \<not>winning_opponent xs))"
    unfolding won_by_player_def by auto

  definition won_by_opponent :: "'v \<Rightarrow> bool" where
    "won_by_opponent v \<equiv> v\<in>V \<and> (\<exists>\<sigma>. strategy_of (-V\<^sub>\<alpha>) \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy (dom \<sigma>) \<sigma>) v xs \<longrightarrow> winning_opponent xs))"

  lemma "won_by_opponent v \<Longrightarrow> (\<exists>\<sigma>. strategy_of (-V\<^sub>\<alpha>) \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy (dom \<sigma>) \<sigma>) v xs \<longrightarrow> \<not>winning_player xs))"
    unfolding won_by_opponent_def by auto

  lemma V\<^sub>\<alpha>_induced_succs_1: "v\<in>V\<^sub>\<alpha> \<Longrightarrow> strategy_of (-V\<^sub>\<alpha>) \<sigma>' \<Longrightarrow> induced_by_strategy (dom \<sigma>') \<sigma>' `` {v} = E `` {v}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def V\<^sub>1_def by auto

  lemma V\<^sub>\<alpha>_induced_succs_2: "v\<in>V\<^sub>\<alpha> \<Longrightarrow> strategy_of V\<^sub>\<alpha> \<sigma> \<Longrightarrow> induced_by_strategy (dom \<sigma>) \<sigma> `` {v} \<noteq> {}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def
    using succ[of v] V\<^sub>\<alpha>_subset
    apply (cases "v\<in>dom \<sigma>")
    subgoal by auto
    subgoal by blast
    done

  lemma V_opp_induced_succs_1: "v\<in>-V\<^sub>\<alpha> \<Longrightarrow> strategy_of V\<^sub>\<alpha> \<sigma>' \<Longrightarrow> induced_by_strategy (dom \<sigma>') \<sigma>' `` {v} = E `` {v}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def V\<^sub>1_def by auto

  lemma V_opp_induced_succs_2: "v\<in>V-V\<^sub>\<alpha> \<Longrightarrow> strategy_of (-V\<^sub>\<alpha>) \<sigma> \<Longrightarrow> induced_by_strategy (dom \<sigma>) \<sigma> `` {v} \<noteq> {}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def V\<^sub>1_def
    using succ[of v] apply (cases "v\<in>dom \<sigma>") by auto

  lemma w1: "won_by_player v \<Longrightarrow> \<not>won_by_opponent v"
    unfolding won_by_player_def won_by_opponent_def
  proof clarsimp
    fix \<sigma> \<sigma>'
    define G\<sigma> where "G\<sigma> = induced_by_strategy (dom \<sigma>) \<sigma>"
    define G\<sigma>' where "G\<sigma>' = induced_by_strategy (dom \<sigma>') \<sigma>'"
    assume \<sigma>_player: "strategy_of V\<^sub>\<alpha> \<sigma>"
      and \<sigma>_win: "\<forall>xs. cycle_from_node G\<sigma> v xs \<longrightarrow> winningP (top_priority xs)"
      and \<sigma>'_opp: "strategy_of (-V\<^sub>\<alpha>) \<sigma>'"
      and "v\<in>V"
    interpret Ginter: arena_defs "G\<sigma> \<inter> G\<sigma>'" V V\<^sub>0 prio
      apply unfold_locales
      subgoal unfolding G\<sigma>_def using ind_subgraph E_in_V by blast
      subgoal by simp
      subgoal proof cases
        fix v
        assume v_in_V\<^sub>\<alpha>: "v\<in>V\<^sub>\<alpha>"
        with \<sigma>'_opp have "G\<sigma>' `` {v} = E `` {v}"
          unfolding G\<sigma>'_def by (simp add: V\<^sub>\<alpha>_induced_succs_1)
        moreover from v_in_V\<^sub>\<alpha> \<sigma>_player have "G\<sigma> `` {v} \<noteq> {}"
          unfolding G\<sigma>_def by (simp add: V\<^sub>\<alpha>_induced_succs_2)
        moreover note succ[of v]
        moreover have "G\<sigma> \<subseteq> E" using ind_subgraph E_in_V by (simp add: G\<sigma>_def)
        ultimately show "(G\<sigma> \<inter> G\<sigma>') `` {v} \<noteq> {}" by fast
      next
        fix v
        assume "v\<in>V" "v\<notin>V\<^sub>\<alpha>"
        hence v_in_Vopp: "v\<in>V-V\<^sub>\<alpha>" by auto
        with \<sigma>_player have "G\<sigma> `` {v} = E `` {v}"
          unfolding G\<sigma>_def by (simp add: V_opp_induced_succs_1)
        moreover from v_in_Vopp \<sigma>'_opp have "G\<sigma>' `` {v} \<noteq> {}"
          unfolding G\<sigma>'_def by (simp add: V_opp_induced_succs_2)
        moreover note succ[of v]
        moreover have "G\<sigma>' \<subseteq> E" using ind_subgraph E_in_V by (simp add: G\<sigma>'_def)
        ultimately show "(G\<sigma> \<inter> G\<sigma>') `` {v} \<noteq> {}" by fast
      qed
      subgoal by (rule V\<^sub>0_in_V)
      done
    from Ginter.finite_graph_always_has_cycle_from_node[OF \<open>v\<in>V\<close>] Ginter.succ \<open>v\<in>V\<close>
    obtain xs where xs: "cycle_from_node (G\<sigma> \<inter> G\<sigma>') v xs" by blast
    moreover from xs have "cycle_from_node G\<sigma> v xs" using cycle_from_node_inter_1 by fastforce
    with \<sigma>_win have "winningP (top_priority xs)" by blast
    moreover from xs have "cycle_from_node G\<sigma>' v xs" using cycle_from_node_inter_2 by fastforce
    ultimately show "\<exists>xs. cycle_from_node (G\<sigma>') v xs \<and> winning_player xs" by blast
  qed

  corollary "\<not>(won_by_player v \<and> won_by_opponent v)" using w1 by blast

end

term "player_arena.won_by_player E V prio V\<^sub>\<alpha> winningP"

lemma card_induct[consumes 1, case_names less]:
  fixes V :: "'a set"
  assumes FIN: "finite V"
  assumes STEP: "\<And>V. \<lbrakk> \<And>V'. \<lbrakk> finite V'; card V' < card V \<rbrakk> \<Longrightarrow> P V' \<rbrakk> \<Longrightarrow> P V"
  shows "P V"
proof -

  have "wf (measure card)" by simp
  then show "P V" using FIN
    apply (induction rule: wf_induct_rule)
    apply simp using STEP .

qed

context finite_graph_V begin
  lemma restrict_graph:
    assumes "V' \<subseteq> V"
    assumes "E' \<subseteq> ((E\<union>Id) \<inter> V'\<times>V')"
    assumes succ: "\<And>v. v\<in>V' \<Longrightarrow> E'``{v}\<noteq>{}"
    shows "finite_graph_V E' V'"
    using assms apply unfold_locales
    by (auto dest: finite_subset)

end

context arena_defs begin

  lemma restrict_arena:
    assumes "V' \<subseteq> V"
    assumes "E' \<subseteq> ((E\<union>Id) \<inter> V'\<times>V')"
    assumes succ: "\<And>v. v\<in>V' \<Longrightarrow> E'``{v}\<noteq>{}"
    assumes "V\<^sub>0' \<subseteq> V'"
    shows "arena_defs E' V' V\<^sub>0'"
    apply intro_locales
    using restrict_graph[OF assms(1,2,3)] apply blast
    apply unfold_locales
    by fact

end

context player_arena begin
  lemma restrict_player_arena:
    assumes "V' \<subseteq> V"
    assumes "E' \<subseteq> ((E\<union>Id) \<inter> V'\<times>V')"
    assumes succ: "\<And>v. v\<in>V' \<Longrightarrow> E'``{v}\<noteq>{}"
    assumes "V\<^sub>0' \<subseteq> V'"
    assumes "V\<^sub>\<alpha>' \<subseteq> V'"
    shows "player_arena E' V' V\<^sub>0' V\<^sub>\<alpha>'"
    apply intro_locales
    using restrict_graph[OF assms(1,2,3)] apply blast
    apply unfold_locales
    by fact+

end





lemma aux:
  fixes v :: 'v
  assumes player_arena: "player_arena E V V\<^sub>0 V\<^sub>\<alpha>"
  assumes "v\<in>V"
  shows "player_arena.won_by_player E V prio V\<^sub>\<alpha> winningP v \<or> player_arena.won_by_opponent E V prio V\<^sub>\<alpha> winningP v"
proof -

  have "finite V" proof -
    interpret player_arena E V V\<^sub>0 prio V\<^sub>\<alpha> winningP by fact
    show ?thesis by blast
  qed
  then show ?thesis using assms
  proof (induction arbitrary: E V\<^sub>0 V\<^sub>\<alpha> v rule: card_induct)
    case (less V)

    interpret player_arena E V V\<^sub>0 prio V\<^sub>\<alpha> winningP by fact

    obtain E' :: "'v rel" and V' V\<^sub>0' V\<^sub>\<alpha>'
      where ARENA': "player_arena E' V' V\<^sub>0' V\<^sub>\<alpha>'" and FIN: "finite V'" and LESS: "card V' < card V"
      sorry

    interpret subgame: player_arena E' V' V\<^sub>0' prio V\<^sub>\<alpha>' winningP
      using ARENA' by auto

    note IH = less.IH[OF FIN LESS ARENA'[unfolded X]]

    show "won_by_player v \<or> won_by_opponent v" sorry
  qed


  sorry

context player_arena begin

  lemma "v\<in>V \<Longrightarrow> won_by_player v \<or> won_by_opponent v"
    using aux player_arena_axioms by metis

end



  term won_by_even

  find_consts name: won






  print_context















    lemma attractor'_intros:
      "\<And>x. x \<in> X \<Longrightarrow> x \<in> attractor' X 0"
      "\<And>x y i. \<lbrakk>x \<in> V\<^sub>\<alpha> - X; (x, y) \<in> E; y\<in>attractor' X i\<rbrakk> \<Longrightarrow> x \<in> attractor' X (Suc i)"
      "\<And>x i. \<lbrakk>x \<in> V - V\<^sub>\<alpha> - X; \<forall>y. (x, y) \<in> E \<longrightarrow> y\<in>attractor' X i\<rbrakk> \<Longrightarrow> x \<in> attractor' X (Suc i)"
      unfolding attractor'_def
      by (auto intro: attractor'p.intros)

    lemma attractor'_subset: assumes "x\<in>attractor' X i" shows "x\<in>attractor X"
      using assms apply (induction rule: attractor'_induct)
      by (auto intro: attractor.intros)

    lemma attractor_subset': assumes "x\<in>attractor X" shows "\<exists>i. x\<in>attractor' X i"
      using assms
    proof (induction rule: attractor.induct)
      case (base x)
      then show ?case by (auto intro: attractor'_intros)
    next
      case (own x y)
      then show ?case by (auto intro: attractor'_intros)
    next
      case (opponent x)
      obtain y where E: "(x,y)\<in>E" using opponent.hyps succ by auto
      with opponent.IH obtain i where "y \<in> attractor X" "y \<in> attractor' X i" by blast
      hence "x \<in> attractor' X (Suc i)"
        using opponent E

        apply (rule_tac attractor'_intros(3))
        apply (auto)


      show ?case
    qed
      apply (auto intro: attractor'p.intros)

      using attractor'p.intros



    lemma attractor_strategy_forces_X: "y\<in>attractor' X n \<Longrightarrow> \<exists>\<sigma>.
       strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> \<subseteq> attractor X - X
       \<and> (\<forall>xs z. path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs z \<and> n<length xs \<longrightarrow> xs!n \<in> X)"
    proof (induction rule: attractor'_induct)
      case (base x)
      then show ?case
        apply -
        apply (rule exI[where x=Map.empty])
        by (auto simp: neq_Nil_conv)

    next
      case (own x y i)

      from own have x_in_attr: "x\<in>attractor X" by (blast intro: attractor.own)

      from own obtain \<sigma> where
        IH_strat: "strategy_of V\<^sub>\<alpha> \<sigma>" and
        IH_dom: "dom \<sigma> \<subseteq> attractor X - X"  and
        IH_lasso: "(\<forall>xs. lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs \<longrightarrow> X \<inter> set xs \<noteq> {})"
        by blast

      show ?case proof (intro exI[where x="\<sigma>(x\<mapsto>y)"] conjI)
        show "strategy_of V\<^sub>\<alpha> (\<sigma>(x \<mapsto> y))" using IH_strat \<open>x\<in>V\<^sub>\<alpha>-X\<close> \<open>(x,y)\<in>E\<close>
          unfolding strategy_of_def E_of_strat_def
          by (auto split: if_splits)
        show "dom (\<sigma>(x \<mapsto> y)) \<subseteq> attractor X - X"
          using IH_dom \<open>x\<in>V\<^sub>\<alpha>-X\<close> x_in_attr by simp

        show "\<forall>xs. lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (\<sigma>(x \<mapsto> y))) x xs \<longrightarrow> X \<inter> set xs \<noteq> {}"
        proof (intro allI impI)
          fix xs
          assume A: "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (\<sigma>(x \<mapsto> y))) x xs"
          hence [simp]: "xs\<noteq>[]" by auto

          have EDGE_DET: "y'=y" if "(x, y') \<in> induced_by_strategy V\<^sub>\<alpha> (\<sigma>(x \<mapsto> y))" for y'
            using that \<open>x\<in>V\<^sub>\<alpha>-X\<close> unfolding induced_by_strategy_def E_of_strat_def
            by auto

          from A obtain z where "path' (induced_by_strategy V\<^sub>\<alpha> (\<sigma>(x \<mapsto> y))) x xs z" "z\<in>set xs"
            using lasso'_iff_path by fast

          then obtain xs' where [simp]: "xs=x#xs'" and path_xs': "path' (induced_by_strategy V\<^sub>\<alpha> (\<sigma>(x \<mapsto> y))) y xs' z"
            apply (cases xs; simp)
            apply (auto dest: EDGE_DET)
            done

          show "X \<inter> set xs \<noteq> {}" proof (cases "z\<in>set xs'")
            case True with path_xs' have "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (\<sigma>(x \<mapsto> y))) y xs'"
              using lasso'_iff_path by fastforce
            with own.IH show ?thesis by simp
          next
            case False show ?thesis proof
              assume xs_no_X: "X \<inter> set xs = {}"
              from False z_back have [simp]: "x = z" by fast
              show False proof (cases xs')
                case Nil with path_xs' x_lasso' xs_no_X own.IH show ?thesis by fastforce
              next
                case (Cons a list)
                hence "xs'\<noteq>[]" by simp
                from lasso'_close_loop[OF path_xs' this] x'_edge
                have "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) y (xs' @ [x])" by auto
                with own.IH xs_no_X show ?thesis by fastforce
              qed
            qed
          qed



          show "X \<inter> set xs \<noteq> {}"




      then show ?case sorry
    next
      case (opponent x i)
      then show ?case sorry
    qed


(**  Commenting this out because it breaks everything else.
    lemma attractor_strategy_forces_X: "y\<in>attractor X \<Longrightarrow> \<exists>\<sigma> n.
       strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> \<subseteq> attractor X - X
       \<and> (\<forall>xs z. path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs z \<and> n\<le>length xs \<longrightarrow> X \<inter> set xs \<noteq> {})"
    proof (induction rule: attractor.induct)
      case (base x) then show ?case
        apply (rule_tac exI[where x=Map.empty])
        using origin_in_lasso' by fastforce
    next
      case (own x y)

      from own have x_in_attr: "x\<in>attractor X" by (blast intro: attractor.own)

      from own obtain \<sigma> where
        IH_strat: "strategy_of V\<^sub>\<alpha> \<sigma>" and
        IH_dom: "dom \<sigma> \<subseteq> attractor X - X"  and
        IH_lasso: "(\<forall>xs. lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs \<longrightarrow> X \<inter> set xs \<noteq> {})"
        by blast

      show ?case proof (intro exI[where x="\<sigma>(x\<mapsto>y)"] conjI)
        show "strategy_of V\<^sub>\<alpha> (\<sigma>(x \<mapsto> y))" using IH_strat \<open>x\<in>V\<^sub>\<alpha>-X\<close> \<open>(x,y)\<in>E\<close>
          unfolding strategy_of_def E_of_strat_def
          by (auto split: if_splits)
        show "dom (\<sigma>(x \<mapsto> y)) \<subseteq> attractor X - X"
          using IH_dom \<open>x\<in>V\<^sub>\<alpha>-X\<close> x_in_attr by simp

        show "\<forall>xs. lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (\<sigma>(x \<mapsto> y))) x xs \<longrightarrow> X \<inter> set xs \<noteq> {}"
        proof (intro allI impI)
          fix xs
          assume A: "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (\<sigma>(x \<mapsto> y))) x xs"
          hence [simp]: "xs\<noteq>[]" by auto

          have EDGE_DET: "y'=y" if "(x, y') \<in> induced_by_strategy V\<^sub>\<alpha> (\<sigma>(x \<mapsto> y))" for y'
            using that \<open>x\<in>V\<^sub>\<alpha>-X\<close> unfolding induced_by_strategy_def E_of_strat_def
            by auto

          from A obtain z where "path' (induced_by_strategy V\<^sub>\<alpha> (\<sigma>(x \<mapsto> y))) x xs z" "z\<in>set xs"
            using lasso'_iff_path by fast

          then obtain xs' where [simp]: "xs=x#xs'" and path_xs': "path' (induced_by_strategy V\<^sub>\<alpha> (\<sigma>(x \<mapsto> y))) y xs' z"
            apply (cases xs; simp)
            apply (auto dest: EDGE_DET)
            done

          show "X \<inter> set xs \<noteq> {}" proof (cases "z\<in>set xs'")
            case True with path_xs' have "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (\<sigma>(x \<mapsto> y))) y xs'"
              using lasso'_iff_path by fastforce
            with own.IH show ?thesis by simp
          next
            case False show ?thesis proof
              assume xs_no_X: "X \<inter> set xs = {}"
              from False z_back have [simp]: "x = z" by fast
              show False proof (cases xs')
                case Nil with path_xs' x_lasso' xs_no_X own.IH show ?thesis by fastforce
              next
                case (Cons a list)
                hence "xs'\<noteq>[]" by simp
                from lasso'_close_loop[OF path_xs' this] x'_edge
                have "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) y (xs' @ [x])" by auto
                with own.IH xs_no_X show ?thesis by fastforce
              qed
            qed
          qed



          show "X \<inter> set xs \<noteq> {}"


      then show ?case
      hence "(x,y) \<in> attractor_edges X" using ae_own attractor_edges_complete by blast
      hence y_only_succ: "induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X) `` {x} = {y}"
        (** Intuitively this is true, but I need some way to prove this, probably some lemma *) sorry
      show ?case proof (rule allI; rule impI)
        fix xs assume x_lasso': "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) x xs"
        from x_lasso' obtain z where x_path': "path' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) x xs z" "z \<in> set xs"
          using lasso'_iff_path by fast
        then obtain x' xs' where
          [simp]:"xs=x#xs'"
          and x'_edge: "(x,x')\<in>(induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X))"
          and path_xs': "path' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) x' xs' z"
          and z_back: "z\<in>insert x (set xs')"
          using path'D by fastforce
        with y_only_succ have [simp]: "x' = y" by blast
        show "X \<inter> set xs \<noteq> {}" proof (cases "z\<in>set xs'")
          case True with path_xs' have "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) y xs'"
            using lasso'_iff_path by fastforce
          with own.IH show ?thesis by simp
        next
          case False show ?thesis proof
            assume xs_no_X: "X \<inter> set xs = {}"
            from False z_back have [simp]: "x = z" by fast
            show False proof (cases xs')
              case Nil with path_xs' x_lasso' xs_no_X own.IH show ?thesis by fastforce
            next
              case (Cons a list)
              hence "xs'\<noteq>[]" by simp
              from lasso'_close_loop[OF path_xs' this] x'_edge
              have "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) y (xs' @ [x])" by auto
              with own.IH xs_no_X show ?thesis by fastforce
            qed
          qed
        qed
      qed
    next
      case (opponent x) show ?case proof (rule allI; rule impI)
        fix xs assume x_lasso': "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) x xs"
        from x_lasso' obtain z where x_path': "path' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) x xs z" "z \<in> set xs"
          using lasso'_iff_path by fast
        then obtain x' xs' where
          [simp]:"xs=x#xs'"
          and x'_edge: "(x,x')\<in>(induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X))"
          and path_xs': "path' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) x' xs' z"
          and z_back: "z\<in>insert x (set xs')"
          using path'D by fastforce
        show "X \<inter> set xs \<noteq> {}" proof (cases "z\<in>set xs'")
          case True
          with path_xs' have "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) x' xs'"
            using lasso'_iff_path by fast
          with x'_edge opponent.IH show ?thesis by force
        next
          case False show ?thesis proof
            assume xs_no_X: "X \<inter> set xs = {}"
            from False z_back have [simp]: "x = z" by fast
            show False proof (cases xs')
              case Nil with path_xs' x'_edge x_lasso' xs_no_X opponent.IH show ?thesis by force
            next
              case (Cons a list)
              hence "xs'\<noteq>[]" by fast
              from lasso'_close_loop[OF path_xs' this] x'_edge
              have "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) x' (xs' @ [x])" by simp
              with opponent.IH x'_edge xs_no_X show ?thesis by force
            qed
          qed
        qed
      qed
    qed *)

    lemma attractor_strategy_forces_X: "y\<in>attractor X
       \<Longrightarrow> \<forall>xs. lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) y xs \<longrightarrow> X \<inter> set xs \<noteq> {}"
    proof (induction rule: attractor.induct)
      case (base x) show ?case proof (rule allI; rule impI)
        fix xs assume "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) x xs"
        from base origin_in_lasso'[OF this] show "X \<inter> set xs \<noteq> {}" by auto
      qed
    next
      case (own x y)
      hence "(x,y) \<in> attractor_edges X" using ae_own attractor_edges_complete by blast
      hence y_only_succ: "induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X) `` {x} = {y}"
        (** Intuitively this is true, but I need some way to prove this, probably some lemma *) sorry
      show ?case proof (rule allI; rule impI)
        fix xs assume x_lasso': "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) x xs"
        from x_lasso' obtain z where x_path': "path' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) x xs z" "z \<in> set xs"
          using lasso'_iff_path by fast
        then obtain x' xs' where
          [simp]:"xs=x#xs'"
          and x'_edge: "(x,x')\<in>(induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X))"
          and path_xs': "path' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) x' xs' z"
          and z_back: "z\<in>insert x (set xs')"
          using path'D by fastforce
        with y_only_succ have [simp]: "x' = y" by blast
        show "X \<inter> set xs \<noteq> {}" proof (cases "z\<in>set xs'")
          case True with path_xs' have "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) y xs'"
            using lasso'_iff_path by fastforce
          with own.IH show ?thesis by simp
        next
          case False show ?thesis proof
            assume xs_no_X: "X \<inter> set xs = {}"
            from False z_back have [simp]: "x = z" by fast
            show False proof (cases xs')
              case Nil with path_xs' x_lasso' xs_no_X own.IH show ?thesis by fastforce
            next
              case (Cons a list)
              hence "xs'\<noteq>[]" by simp
              from lasso'_close_loop[OF path_xs' this] x'_edge
              have "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) y (xs' @ [x])" by auto
              with own.IH xs_no_X show ?thesis by fastforce
            qed
          qed
        qed
      qed
    next
      case (opponent x) show ?case proof (rule allI; rule impI)
        fix xs assume x_lasso': "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) x xs"
        from x_lasso' obtain z where x_path': "path' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) x xs z" "z \<in> set xs"
          using lasso'_iff_path by fast
        then obtain x' xs' where
          [simp]:"xs=x#xs'"
          and x'_edge: "(x,x')\<in>(induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X))"
          and path_xs': "path' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) x' xs' z"
          and z_back: "z\<in>insert x (set xs')"
          using path'D by fastforce
        show "X \<inter> set xs \<noteq> {}" proof (cases "z\<in>set xs'")
          case True
          with path_xs' have "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) x' xs'"
            using lasso'_iff_path by fast
          with x'_edge opponent.IH show ?thesis by force
        next
          case False show ?thesis proof
            assume xs_no_X: "X \<inter> set xs = {}"
            from False z_back have [simp]: "x = z" by fast
            show False proof (cases xs')
              case Nil with path_xs' x'_edge x_lasso' xs_no_X opponent.IH show ?thesis by force
            next
              case (Cons a list)
              hence "xs'\<noteq>[]" by fast
              from lasso'_close_loop[OF path_xs' this] x'_edge
              have "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)) x' (xs' @ [x])" by simp
              with opponent.IH x'_edge xs_no_X show ?thesis by force
            qed
          qed
        qed
      qed
    qed

    lemma "\<exists>\<sigma>.
        strategy_of V\<^sub>\<alpha> \<sigma>
      \<and> dom \<sigma> \<subseteq> attractor X
      \<and> (\<forall>y\<in>attractor X. \<forall>xs. lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs \<longrightarrow> X \<inter> set xs \<noteq> {})"
    proof -
      fix \<sigma>
      define \<sigma> where "\<sigma> = attractor_strategy X"
      show ?thesis proof (rule exI[where x="\<sigma>"]; intro conjI)
        show "strategy_of V\<^sub>\<alpha> \<sigma>" using \<sigma>_def attractor_strategy_of_V\<^sub>\<alpha> by blast
      next
        show "dom \<sigma> \<subseteq> attractor X" using \<sigma>_def dom_attractor_strategy by blast
      next
        show "\<forall>y\<in>attractor X. \<forall>xs. lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs \<longrightarrow> X \<inter> set xs \<noteq> {}"
          using \<sigma>_def attractor_strategy_forces_X by blast
      qed
    qed

    lemma attract_strategy_aux: "is_attractor X Y \<Longrightarrow> \<exists>\<sigma>.
          strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> \<subseteq> Y \<and> (induced_by_strategy V\<^sub>\<alpha> \<sigma> `` (Y-X) \<subseteq> Y)
          \<and> (\<forall>y\<in>Y. \<forall>xs. lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs \<longrightarrow> X \<inter> set xs \<noteq> {})"
    proof (induction rule: is_attractor.induct)
      case base thus ?case
        apply (rule exI[where x=Map.empty]; simp)
        using origin_in_lasso' by fastforce
    next
      case (step Y Y')
      note Y'_def = step.hyps
      from step.IH obtain \<sigma> where
       PLAYER_\<sigma> [simp]: "strategy_of V\<^sub>\<alpha> \<sigma>"
       and DOM_\<sigma>: "dom \<sigma> \<subseteq> Y"
       and Y_CLOSED_\<sigma>: "(induced_by_strategy V\<^sub>\<alpha> \<sigma> `` (Y-X) \<subseteq> Y)"
       and ATTR_\<sigma>: "(\<forall>y\<in>Y. \<forall>xs. lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs \<longrightarrow> X \<inter> set xs \<noteq> {})"
        by blast

      fix \<sigma>' :: "'v \<rightharpoonup> 'v"
      let ?dom' = "owned_target Y - Y"
      define \<sigma>' where "\<sigma>' = (\<lambda>v. (
        if v\<in>?dom' then Some (SOME v'. v'\<in>E``{v} \<inter> Y)
        else None))"
      have EDGE_\<sigma>': "\<forall>u v. \<sigma>' u = Some v \<longrightarrow> (u,v)\<in>E"
        unfolding \<sigma>'_def apply (auto) by (metis (no_types, lifting) someI)
      have DOM_\<sigma>': "dom \<sigma>' = owned_target Y - Y"
        unfolding \<sigma>'_def by (auto split: if_splits)
      have RAN_\<sigma>': "ran \<sigma>' \<subseteq> Y"
        unfolding \<sigma>'_def apply (auto simp: ran_def) by (metis (no_types, lifting) someI)
      have PLAYER_\<sigma>'[simp]: "strategy_of V\<^sub>\<alpha> \<sigma>'"
        unfolding strategy_of_def E_of_strat_def using DOM_\<sigma>' EDGE_\<sigma>' by auto

      from DOM_\<sigma> DOM_\<sigma>' have DOMS_DISJ[simp]: "dom \<sigma> \<inter> dom \<sigma>' = {}" by auto

      let ?iE' = "(induced_by_strategy V\<^sub>\<alpha> \<sigma> \<union> E_of_strat \<sigma>')"
      have NO_Y_\<sigma>': "fst`E_of_strat \<sigma>' \<inter> Y = {}"
        using DOM_\<sigma>' by (simp add: E_of_strat_dom inf_commute)
      with Y_CLOSED_\<sigma> have Y_CLOSED_\<sigma>': "?iE'``(Y-X) \<subseteq> Y" by auto

      {
        fix y xs
        assume y: "y\<in>Y"
        assume y_lasso': "lasso_from_node' ?iE' y xs"
        from y_lasso' obtain y' where y_path': "path' ?iE' y xs y'" "y'\<in>set xs"
          by (auto simp: lasso'_iff_path)

        from simulate_path_aux[OF Y_CLOSED_\<sigma>' y y_path'(1)] have "X \<inter> set xs \<noteq> {}"
        proof
          assume "path' (?iE' \<inter> (Y - X) \<times> Y) y xs y'"
          moreover have "?iE' \<inter> (Y - X) \<times> Y \<subseteq> induced_by_strategy V\<^sub>\<alpha> \<sigma>" using NO_Y_\<sigma>' by auto
          ultimately have "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs y'" using subgraph_path' by meson
          with y_path'(2) have "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs"
            by (auto simp: lasso'_iff_path)
          with ATTR_\<sigma>[rule_format, OF y] show "X \<inter> set xs \<noteq> {}" by blast
        qed
      } note IN_Y_DONE = this

      {
        fix y xs
        assume y: "y \<in> Y'" and y_lasso: "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>')) y xs"
        from subgraph_lasso'[OF ind_subgraph_addD, OF y_lasso]
        have y_lasso': "lasso_from_node' ?iE' y xs" .

        have "X \<inter> set xs \<noteq> {}"
        proof cases
          assume "y\<in>X"
          moreover from y_lasso origin_in_lasso' have "y\<in>set xs" by fast
          ultimately show ?thesis by auto
        next
          assume "y\<notin>X"
          from y consider "y\<in>Y" | "y\<in>?dom'" | "y\<in>opponent_target Y" unfolding Y'_def by blast
          then have "X \<inter> set xs \<noteq> {}"
          proof cases
            assume "y\<in>Y" thus ?thesis using IN_Y_DONE y_lasso' by blast
          next
            assume y_in_dom': "y\<in>?dom'"
            from y_lasso' obtain y'' where y_path': "path' ?iE' y xs y''" "y''\<in>set xs"
              by (auto simp: lasso'_iff_path)

            have "?iE' `` {y} \<subseteq> Y"
            proof -
              have "E_of_strat \<sigma>' `` {y} \<subseteq> Y" using RAN_\<sigma>' by simp
              moreover have "induced_by_strategy V\<^sub>\<alpha> \<sigma> `` {y} \<subseteq> Y"
                using y_in_dom' DOM_\<sigma> unfolding induced_by_strategy_def E_of_strat_def by auto
              ultimately show ?thesis by auto
            qed

            with y_path' obtain y' xs' where
              [simp]: "xs=y#xs'"
              and y'_in_Y: "y'\<in>Y"
              and path_xs': "path' ?iE' y' xs' y''"
              and y''_back: "y''\<in>insert y (set xs')"
              apply (cases xs) by auto

            show ?thesis
            proof (cases "y''\<in> set xs'")
              case True thus ?thesis
                using IN_Y_DONE[OF y'_in_Y] path_xs' lasso'_iff_path by fastforce
            next
              case False show ?thesis proof
                assume xs_no_X: "X \<inter> set xs = {}"

                from False y''_back have [simp]: "y''=y" by auto
                have "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma> \<inter> UNIV \<times> Y) y' xs' y"
                proof -
                  from simulate_path_aux[OF Y_CLOSED_\<sigma>' y'_in_Y path_xs']
                  have "path' (?iE' \<inter> (Y - X) \<times> Y) y' xs' y" using xs_no_X by simp
                  moreover have "(?iE') \<inter> (Y - X) \<times> Y \<subseteq> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<inter> UNIV \<times> Y"
                    using NO_Y_\<sigma>' by auto
                  ultimately show ?thesis by (simp add: subgraph_path')
                qed
                thus False
                  apply (cases xs' rule: rev_cases)
                  using y_in_dom' y'_in_Y by auto
              qed
            qed
          next
            assume y_in_opponent_target: "y\<in>opponent_target Y"
            from y_lasso' obtain y'' where y_path': "path' ?iE' y xs y''" "y''\<in>set xs"
              by (auto simp: lasso'_iff_path)

            have "?iE'``{y} \<subseteq> Y"
            proof -
              from y_in_opponent_target have "E``{y} \<subseteq> Y" by fast
              moreover have "?iE' \<subseteq> E" using PLAYER_\<sigma>' strategy_of_def by auto
              ultimately show ?thesis by blast
            qed

            with y_path' obtain y' xs' where
              [simp]: "xs=y#xs'"
              and y'_in_Y: "y'\<in>Y"
              and path_xs': "path' ?iE' y' xs' y''"
              and y''_back: "y''\<in>insert y (set xs')"
              apply (cases xs)
              by auto

            show ?thesis
            proof (cases "y''\<in> set xs'")
              case True thus ?thesis
                using IN_Y_DONE[OF y'_in_Y] path_xs' lasso'_iff_path
                by fastforce
            next
              case False show ?thesis proof
                assume xs_no_X: "X \<inter> set xs = {}"

                from False y''_back have [simp]: "y''=y" by auto
                have "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma> \<inter> UNIV \<times> Y) y' xs' y"
                proof -
                  from simulate_path_aux[OF Y_CLOSED_\<sigma>' y'_in_Y path_xs']
                  have "path' (?iE' \<inter> (Y - X) \<times> Y) y' xs' y" using xs_no_X by simp
                  moreover have "(?iE') \<inter> (Y - X) \<times> Y \<subseteq> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<inter> UNIV \<times> Y"
                    using NO_Y_\<sigma>' by auto
                  ultimately show ?thesis by (simp add: subgraph_path')
                qed
                thus False
                  apply (cases xs' rule: rev_cases)
                  using IN_Y_DONE[OF y'_in_Y] y_lasso' xs_no_X apply fastforce
                  apply simp
                  using IN_Y_DONE y_lasso' xs_no_X by blast
              qed
            qed
          qed
          thus ?thesis .
        qed
      } note aux = this

      have aux2: "induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>') `` (Y' - X) \<subseteq> Y'"
      proof clarify
        fix x y
        assume edge: "(x,y) \<in> induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>')" "x \<in> Y'" "x \<notin> X"
        then consider "x\<in>Y" | "x\<in>?dom'" | "x\<in>opponent_target Y" unfolding Y'_def by blast
        thus "y \<in> Y'" proof cases
          case 1
          have "(x,y) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>"
          proof -
            from ind_subgraph_add_edge_src[OF edge(1)] have "x \<in> dom \<sigma> \<or> x \<in> dom \<sigma>' \<or> x \<in> (-V\<^sub>\<alpha>)" .
            with 1 consider "x \<in> dom \<sigma>" | "x \<in> (-V\<^sub>\<alpha>)" using DOM_\<sigma>' by force
            thus ?thesis proof cases
              case 1 from ind_subgraph_add_edge_dom_\<sigma>[OF edge(1) DOMS_DISJ this] show ?thesis .
            next
              case 2 from ind_subgraph_add_edge_outside_strat[OF edge(1) this] show ?thesis ..
            qed
          qed
          moreover from 1 edge have "x \<in> Y-X" by blast
          ultimately show ?thesis
            using Y_CLOSED_\<sigma> unfolding Y'_def by auto
        next
          case 2
          with DOM_\<sigma>' have "x \<in> dom \<sigma>'" by simp
          from ind_subgraph_add_edge_dom_\<sigma>'[OF edge(1) this]
          have xy_in_\<sigma>'_subgraph:"(x,y) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>'" .
          from 2 have x_V\<^sub>0: "x \<in> V\<^sub>\<alpha>" unfolding Y'_def by fast
          from ind_subgraph_edge_dst[OF xy_in_\<sigma>'_subgraph x_V\<^sub>0] RAN_\<sigma>'
          show ?thesis unfolding Y'_def by auto
        next
          case 3
          hence "E``{x} \<subseteq> Y" by blast
          moreover from edge have "(x,y) \<in> E" by simp
          ultimately show ?thesis unfolding Y'_def by auto
        qed
      qed

      show ?case
        apply (rule exI[where x="\<sigma> ++ \<sigma>'"])
        apply (auto simp: aux aux2)
        using DOM_\<sigma> DOM_\<sigma>' by (auto simp: Y'_def)
    qed


   (** lemma attract_strategy_aux: "is_attractor X Y \<Longrightarrow> \<exists>\<sigma>.
          strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> \<subseteq> Y \<and> (induced_by_strategy V\<^sub>\<alpha> \<sigma> `` (Y-X) \<subseteq> Y)
          \<and> (\<forall>y\<in>Y. \<forall>xs. lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs \<longrightarrow> X \<inter> set xs \<noteq> {})"
    proof (induction rule: is_attractor.induct)
      case base thus ?case
        apply (rule exI[where x=Map.empty]; simp)
        using origin_in_lasso' by fastforce
    next
      case (step Y Y')
      note Y'_def = step.hyps
      from step.IH obtain \<sigma> where
       PLAYER_\<sigma> [simp]: "strategy_of V\<^sub>\<alpha> \<sigma>"
       and DOM_\<sigma>: "dom \<sigma> \<subseteq> Y"
       and Y_CLOSED_\<sigma>: "(induced_by_strategy V\<^sub>\<alpha> \<sigma> `` (Y-X) \<subseteq> Y)"
       and ATTR_\<sigma>: "(\<forall>y\<in>Y. \<forall>xs. lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs \<longrightarrow> X \<inter> set xs \<noteq> {})"
        by blast

      fix \<sigma>' :: "'v \<rightharpoonup> 'v"
      let ?dom' = "owned_target Y - Y"
      define \<sigma>' where "\<sigma>' = (\<lambda>v. (
        if v\<in>?dom' then Some (SOME v'. v'\<in>E``{v} \<inter> Y)
        else None))"
      have EDGE_\<sigma>': "\<forall>u v. \<sigma>' u = Some v \<longrightarrow> (u,v)\<in>E"
        unfolding \<sigma>'_def apply (auto) by (metis (no_types, lifting) someI)
      have DOM_\<sigma>': "dom \<sigma>' = owned_target Y - Y"
        unfolding \<sigma>'_def by (auto split: if_splits)
      have RAN_\<sigma>': "ran \<sigma>' \<subseteq> Y"
        unfolding \<sigma>'_def apply (auto simp: ran_def) by (metis (no_types, lifting) someI)
      have PLAYER_\<sigma>'[simp]: "strategy_of V\<^sub>\<alpha> \<sigma>'"
        unfolding strategy_of_def E_of_strat_def using DOM_\<sigma>' EDGE_\<sigma>' by auto

      from DOM_\<sigma> DOM_\<sigma>' have DOMS_DISJ[simp]: "dom \<sigma> \<inter> dom \<sigma>' = {}" by auto

      let ?iE' = "(induced_by_strategy V\<^sub>\<alpha> \<sigma> \<union> E_of_strat \<sigma>')"
      have NO_Y_\<sigma>': "fst`E_of_strat \<sigma>' \<inter> Y = {}"
        using DOM_\<sigma>' by (simp add: E_of_strat_dom inf_commute)
      with Y_CLOSED_\<sigma> have Y_CLOSED_\<sigma>': "?iE'``(Y-X) \<subseteq> Y" by auto

      {
        fix y xs
        assume y: "y\<in>Y"
        assume y_lasso': "lasso_from_node' ?iE' y xs"
        from y_lasso' obtain y' where y_path': "path' ?iE' y xs y'" "y'\<in>set xs"
          by (auto simp: lasso'_iff_path)

        from simulate_path_aux[OF Y_CLOSED_\<sigma>' y y_path'(1)] have "X \<inter> set xs \<noteq> {}"
        proof
          assume "path' (?iE' \<inter> (Y - X) \<times> Y) y xs y'"
          moreover have "?iE' \<inter> (Y - X) \<times> Y \<subseteq> induced_by_strategy V\<^sub>\<alpha> \<sigma>" using NO_Y_\<sigma>' by auto
          ultimately have "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs y'" using subgraph_path' by meson
          with y_path'(2) have "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs"
            by (auto simp: lasso'_iff_path)
          with ATTR_\<sigma>[rule_format, OF y] show "X \<inter> set xs \<noteq> {}" by blast
        qed
      } note IN_Y_DONE = this

      {
        fix y xs
        assume y: "y \<in> Y'" and y_lasso: "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>')) y xs"
        from subgraph_lasso'[OF ind_subgraph_addD, OF y_lasso]
        have y_lasso': "lasso_from_node' ?iE' y xs" .

        have "X \<inter> set xs \<noteq> {}"
        proof cases
          assume "y\<in>X"
          moreover from y_lasso origin_in_lasso' have "y\<in>set xs" by fast
          ultimately show ?thesis by auto
        next
          assume "y\<notin>X"
          from y consider "y\<in>Y" | "y\<in>?dom'" | "y\<in>opponent_target Y" unfolding Y'_def by blast
          then have "X \<inter> set xs \<noteq> {}"
          proof cases
            assume "y\<in>Y" thus ?thesis using IN_Y_DONE y_lasso' by blast
          next
            assume y_in_dom': "y\<in>?dom'"
            from y_lasso' obtain y'' where y_path': "path' ?iE' y xs y''" "y''\<in>set xs"
              by (auto simp: lasso'_iff_path)

            have "?iE' `` {y} \<subseteq> Y"
            proof -
              have "E_of_strat \<sigma>' `` {y} \<subseteq> Y" using RAN_\<sigma>' by simp
              moreover have "induced_by_strategy V\<^sub>\<alpha> \<sigma> `` {y} \<subseteq> Y"
                using y_in_dom' DOM_\<sigma> unfolding induced_by_strategy_def E_of_strat_def by auto
              ultimately show ?thesis by auto
            qed

            with y_path' obtain y' xs' where
              [simp]: "xs=y#xs'"
              and y'_in_Y: "y'\<in>Y"
              and path_xs': "path' ?iE' y' xs' y''"
              and y''_back: "y''\<in>insert y (set xs')"
              apply (cases xs) by auto

            show ?thesis
            proof (cases "y''\<in> set xs'")
              case True thus ?thesis
                using IN_Y_DONE[OF y'_in_Y] path_xs' lasso'_iff_path by fastforce
            next
              case False show ?thesis proof
                assume xs_no_X: "X \<inter> set xs = {}"

                from False y''_back have [simp]: "y''=y" by auto
                have "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma> \<inter> UNIV \<times> Y) y' xs' y"
                proof -
                  from simulate_path_aux[OF Y_CLOSED_\<sigma>' y'_in_Y path_xs']
                  have "path' (?iE' \<inter> (Y - X) \<times> Y) y' xs' y" using xs_no_X by simp
                  moreover have "(?iE') \<inter> (Y - X) \<times> Y \<subseteq> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<inter> UNIV \<times> Y"
                    using NO_Y_\<sigma>' by auto
                  ultimately show ?thesis by (simp add: subgraph_path')
                qed
                thus False
                  apply (cases xs' rule: rev_cases)
                  using y_in_dom' y'_in_Y by auto
              qed
            qed
          next
            assume y_in_opponent_target: "y\<in>opponent_target Y"
            from y_lasso' obtain y'' where y_path': "path' ?iE' y xs y''" "y''\<in>set xs"
              by (auto simp: lasso'_iff_path)

            have "?iE'``{y} \<subseteq> Y"
            proof -
              from y_in_opponent_target have "E``{y} \<subseteq> Y" by fast
              moreover have "?iE' \<subseteq> E" using PLAYER_\<sigma>' strategy_of_def by auto
              ultimately show ?thesis by blast
            qed

            with y_path' obtain y' xs' where
              [simp]: "xs=y#xs'"
              and y'_in_Y: "y'\<in>Y"
              and path_xs': "path' ?iE' y' xs' y''"
              and y''_back: "y''\<in>insert y (set xs')"
              apply (cases xs)
              by auto

            show ?thesis
            proof (cases "y''\<in> set xs'")
              case True thus ?thesis
                using IN_Y_DONE[OF y'_in_Y] path_xs' lasso'_iff_path
                by fastforce
            next
              case False show ?thesis proof
                assume xs_no_X: "X \<inter> set xs = {}"

                from False y''_back have [simp]: "y''=y" by auto
                have "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma> \<inter> UNIV \<times> Y) y' xs' y"
                proof -
                  from simulate_path_aux[OF Y_CLOSED_\<sigma>' y'_in_Y path_xs']
                  have "path' (?iE' \<inter> (Y - X) \<times> Y) y' xs' y" using xs_no_X by simp
                  moreover have "(?iE') \<inter> (Y - X) \<times> Y \<subseteq> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<inter> UNIV \<times> Y"
                    using NO_Y_\<sigma>' by auto
                  ultimately show ?thesis by (simp add: subgraph_path')
                qed
                thus False
                  apply (cases xs' rule: rev_cases)
                  using IN_Y_DONE[OF y'_in_Y] y_lasso' xs_no_X apply fastforce
                  apply simp
                  using IN_Y_DONE y_lasso' xs_no_X by blast
              qed
            qed
          qed
          thus ?thesis .
        qed
      } note aux = this

      have aux2: "induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>') `` (Y' - X) \<subseteq> Y'"
      proof clarify
        fix x y
        assume edge: "(x,y) \<in> induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>')" "x \<in> Y'" "x \<notin> X"
        then consider "x\<in>Y" | "x\<in>?dom'" | "x\<in>opponent_target Y" unfolding Y'_def by blast
        thus "y \<in> Y'" proof cases
          case 1
          have "(x,y) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>"
          proof -
            from ind_subgraph_add_edge_src[OF edge(1)] have "x \<in> dom \<sigma> \<or> x \<in> dom \<sigma>' \<or> x \<in> (-V\<^sub>\<alpha>)" .
            with 1 consider "x \<in> dom \<sigma>" | "x \<in> (-V\<^sub>\<alpha>)" using DOM_\<sigma>' by force
            thus ?thesis proof cases
              case 1 from ind_subgraph_add_edge_dom_\<sigma>[OF edge(1) DOMS_DISJ this] show ?thesis .
            next
              case 2 from ind_subgraph_add_edge_outside_strat[OF edge(1) this] show ?thesis ..
            qed
          qed
          moreover from 1 edge have "x \<in> Y-X" by blast
          ultimately show ?thesis
            using Y_CLOSED_\<sigma> unfolding Y'_def by auto
        next
          case 2
          with DOM_\<sigma>' have "x \<in> dom \<sigma>'" by simp
          from ind_subgraph_add_edge_dom_\<sigma>'[OF edge(1) this]
          have xy_in_\<sigma>'_subgraph:"(x,y) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>'" .
          from 2 have x_V\<^sub>0: "x \<in> V\<^sub>\<alpha>" unfolding Y'_def by fast
          from ind_subgraph_edge_dst[OF xy_in_\<sigma>'_subgraph x_V\<^sub>0] RAN_\<sigma>'
          show ?thesis unfolding Y'_def by auto
        next
          case 3
          hence "E``{x} \<subseteq> Y" by blast
          moreover from edge have "(x,y) \<in> E" by simp
          ultimately show ?thesis unfolding Y'_def by auto
        qed
      qed

      show ?case
        apply (rule exI[where x="\<sigma> ++ \<sigma>'"])
        apply (auto simp: aux aux2)
        using DOM_\<sigma> DOM_\<sigma>' by (auto simp: Y'_def)
    qed *)

    theorem attract_strategy:
      assumes "is_attractor X Y"
      obtains \<sigma> where
        "strategy_of V\<^sub>\<alpha> \<sigma>"
        "dom \<sigma> \<subseteq> Y"
        "(\<forall>y\<in>Y. \<forall>xs. lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs \<longrightarrow> X \<inter> set xs \<noteq> {})"
      using attract_strategy_aux[OF assms] by blast

  end

  abbreviation "attr_even \<equiv> attractor V\<^sub>0"
  abbreviation "attr_odd \<equiv> attractor V\<^sub>1"

  thm attract_strategy[where V\<^sub>\<alpha>=V\<^sub>0]
  thm attract_strategy[where V\<^sub>\<alpha>=V\<^sub>1]


  definition won_by_even :: "'v \<Rightarrow> bool" where
    "won_by_even v \<equiv> v\<in>V \<and> (\<exists>\<sigma>. strategy_of V\<^sub>0 \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy (dom \<sigma>) \<sigma>) v xs \<longrightarrow> winning_even xs))"

  lemma "won_by_even v \<Longrightarrow> (\<exists>\<sigma>. strategy_of V\<^sub>0 \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy (dom \<sigma>) \<sigma>) v xs \<longrightarrow> \<not>winning_odd xs))"
    unfolding won_by_even_def by auto

  definition won_by_odd :: "'v \<Rightarrow> bool" where
    "won_by_odd v \<equiv> v\<in>V \<and> (\<exists>\<sigma>. strategy_of V\<^sub>1 \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy (dom \<sigma>) \<sigma>) v xs \<longrightarrow> winning_odd xs))"

  lemma "won_by_odd v \<Longrightarrow> \<exists>\<sigma>. strategy_of V\<^sub>1 \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy (dom \<sigma>) \<sigma>) v xs \<longrightarrow> \<not>winning_even xs)"
    unfolding won_by_odd_def by auto

  lemma V\<^sub>0_induced_succs_1: "v\<in>V\<^sub>0 \<Longrightarrow> strategy_of V\<^sub>1 \<sigma>' \<Longrightarrow> induced_by_strategy (dom \<sigma>') \<sigma>' `` {v} = E `` {v}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def V\<^sub>1_def by auto

  lemma V\<^sub>0_induced_succs_2: "v\<in>V\<^sub>0 \<Longrightarrow> strategy_of V\<^sub>0 \<sigma> \<Longrightarrow> induced_by_strategy (dom \<sigma>) \<sigma> `` {v} \<noteq> {}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def
    using succ[of v] V\<^sub>0_in_V
    apply (cases "v\<in>dom \<sigma>")
    subgoal by auto
    subgoal by blast
    done

  lemma V\<^sub>1_induced_succs_1: "v\<in>V\<^sub>1 \<Longrightarrow> strategy_of V\<^sub>0 \<sigma>' \<Longrightarrow> induced_by_strategy (dom \<sigma>') \<sigma>' `` {v} = E `` {v}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def V\<^sub>1_def by auto

  lemma V\<^sub>1_induced_succs_2: "v\<in>V\<^sub>1 \<Longrightarrow> strategy_of V\<^sub>1 \<sigma> \<Longrightarrow> induced_by_strategy (dom \<sigma>) \<sigma> `` {v} \<noteq> {}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def V\<^sub>1_def
    using succ[of v] apply (cases "v\<in>dom \<sigma>") by auto

  lemma w1: "won_by_even v \<Longrightarrow> \<not>won_by_odd v"
    unfolding won_by_even_def won_by_odd_def
  proof clarsimp
    fix \<sigma> \<sigma>'
    define G\<sigma> where "G\<sigma> = induced_by_strategy (dom \<sigma>) \<sigma>"
    define G\<sigma>' where "G\<sigma>' = induced_by_strategy (dom \<sigma>') \<sigma>'"
    assume \<sigma>_even: "strategy_of V\<^sub>0 \<sigma>"
      and \<sigma>_win: "\<forall>xs. cycle_from_node G\<sigma> v xs \<longrightarrow> even (top_priority xs)"
      and \<sigma>'_odd: "strategy_of V\<^sub>1 \<sigma>'"
      and "v\<in>V"
    interpret Ginter: arena_defs "G\<sigma> \<inter> G\<sigma>'" V V\<^sub>0 prio
      apply unfold_locales
      subgoal unfolding G\<sigma>_def using ind_subgraph E_in_V by blast
      subgoal by simp
      subgoal proof cases
        fix v
        assume v_in_V\<^sub>0: "v\<in>V\<^sub>0"
        with \<sigma>'_odd have "G\<sigma>' `` {v} = E `` {v}"
          unfolding G\<sigma>'_def by (simp add: V\<^sub>0_induced_succs_1)
        moreover from v_in_V\<^sub>0 \<sigma>_even have "G\<sigma> `` {v} \<noteq> {}"
          unfolding G\<sigma>_def by (simp add: V\<^sub>0_induced_succs_2)
        moreover note succ[of v]
        moreover have "G\<sigma> \<subseteq> E" using ind_subgraph E_in_V by (simp add: G\<sigma>_def)
        ultimately show "(G\<sigma> \<inter> G\<sigma>') `` {v} \<noteq> {}" by fast
      next
        fix v
        assume "v\<in>V" "v\<notin>V\<^sub>0"
        hence v_in_V\<^sub>1: "v\<in>V\<^sub>1" unfolding V\<^sub>1_def by auto
        with \<sigma>_even have "G\<sigma> `` {v} = E `` {v}"
          unfolding G\<sigma>_def by (simp add: V\<^sub>1_induced_succs_1)
        moreover from v_in_V\<^sub>1 \<sigma>'_odd have "G\<sigma>' `` {v} \<noteq> {}"
          unfolding G\<sigma>'_def by (simp add: V\<^sub>1_induced_succs_2)
        moreover note succ[of v]
        moreover have "G\<sigma>' \<subseteq> E" using ind_subgraph E_in_V by (simp add: G\<sigma>'_def)
        ultimately show "(G\<sigma> \<inter> G\<sigma>') `` {v} \<noteq> {}" by fast
      qed
      subgoal by (rule V\<^sub>0_in_V)
      done
    from Ginter.finite_graph_always_has_cycle_from_node[OF \<open>v\<in>V\<close>] Ginter.succ \<open>v\<in>V\<close>
    obtain xs where xs: "cycle_from_node (G\<sigma> \<inter> G\<sigma>') v xs" by blast
    moreover from xs have "cycle_from_node G\<sigma> v xs" using cycle_from_node_inter_1 by fastforce
    with \<sigma>_win have "even (top_priority xs)" by blast
    moreover from xs have "cycle_from_node G\<sigma>' v xs" using cycle_from_node_inter_2 by fastforce
    ultimately show "\<exists>xs. cycle_from_node (G\<sigma>') v xs \<and> even (top_priority xs)" by blast
  qed

  (*lemma w': "\<not>won_by_odd v \<Longrightarrow> won_by_even v" unfolding won_by_odd_def won_by_even_def apply clarsimp
  apply (drule spec[where x=\<sigma>1]) apply (subgoal_tac "strategy_of V\<^sub>1 \<sigma>1") apply clarsimp oops

  lemma w2:"won_by_even v \<or> won_by_odd v" oops

  lemma "won_by_even v \<noteq> won_by_odd v" (*using w1 w'*) oops
  *)


  lemma subarenaI:
    assumes "V'\<subseteq>V"
    assumes "\<And>v. v\<in>V' \<Longrightarrow> E``{v} \<inter> V' \<noteq> {}"
    shows "arena_defs (E \<inter> (V'\<times>V')) V' (V\<^sub>0 \<inter> V')"
    apply unfold_locales
    using assms succ
    by (auto intro: finite_subset)



end

  term "arena_defs.won_by_even E V V\<^sub>0 prio"

        find_theorems arg_max

(* TODO: this is a general lemma! *)
lemma obtain_max_arg_finite_set_nat:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "finite S" "S\<noteq>{}"
  obtains s where "s\<in>S" "\<forall>s'\<in>S. f s' \<le> f s"
proof -
  have "\<exists>s\<in>S. \<forall>s'\<in>S. f s' \<le> f s"
    using assms
    apply (induction)
    apply auto
    by force
  thus ?thesis using that by blast
qed




(**
  lemma
    fixes E V V\<^sub>0 and prio :: "'v \<Rightarrow> nat"
    assumes "arena_defs E V V\<^sub>0"
    shows "\<exists>W\<^sub>0 W\<^sub>1. V = W\<^sub>0 \<union> W\<^sub>1 \<and> W\<^sub>0 \<inter> W\<^sub>1 = {} \<and> (\<forall>v\<in>W\<^sub>0. arena_defs.won_by_even E V V\<^sub>0 prio v) \<and> (\<forall>v\<in>W\<^sub>1. arena_defs.won_by_odd E V V\<^sub>0 prio v)"
  proof -
    have "finite V"
    proof -
      from assms interpret arena_defs E V V\<^sub>0 prio .
      show ?thesis by (rule fin_V)
    qed
    then show ?thesis using assms
    proof (induction arbitrary: E V\<^sub>0 rule: finite_psubset_induct)
      case (psubset V)

      interpret arena_defs E V V\<^sub>0 prio by fact

      show ?case proof (cases)
        assume "V={}"
        thus ?thesis by blast
      next
        assume "V\<noteq>{}"

        find_theorems arg_max_on

        find_theorems "_\<noteq>{}" "?a\<in>_" "_ \<le> ?f ?a"

        find_theorems "arg_max_on"

        obtain v where V_NODE: "v\<in>V" and V_MAXP: "\<forall>v'\<in>V. prio v' \<le> prio v"
          using obtain_max_arg_finite_set_nat[OF _ \<open>V\<noteq>{}\<close>, of prio] by blast

        assume WLOG_EVEN: "even (prio v)"

        define A where "A = attr_even "


      then show ?case sorry
    qed *)
end
