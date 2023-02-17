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
  definition V where "V = fst`E \<union> snd`E"

  lemma "finite E \<Longrightarrow> finite V"
    unfolding V_def by simp

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
    apply (induction vs arbitrary: v)
    apply simp by fastforce

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
    case (1 v v')
    then show ?case by simp
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
    apply (induction xs arbitrary: v)
    apply auto by fastforce

  lemma rtrancl_is_path: "(v,v')\<in>E\<^sup>* \<Longrightarrow> \<exists>xs. path v xs v'"
    apply (induction rule: converse_rtrancl_induct)
    using path.simps(1) path.simps(2) by blast+

  lemma path_equiv_rtrancl: "(v,v') \<in> E\<^sup>* \<longleftrightarrow> (\<exists>xs. path v xs v')"
    apply auto by (simp add: rtrancl_is_path path_is_rtrancl)+

  lemma path'_is_rtrancl: "path' v xs v' \<Longrightarrow> (v,v')\<in>E\<^sup>*"
    apply (induction xs arbitrary: v)
    apply auto by fastforce

  lemma rtrancl_is_path': "(v,v')\<in>E\<^sup>* \<Longrightarrow> \<exists>xs. path' v xs v'"
    apply (induction rule: converse_rtrancl_induct)
    using path'.simps(1) path'.simps(2) by blast+

  lemma path'_equiv_rtrancl: "(v,v') \<in> E\<^sup>* \<longleftrightarrow> (\<exists>xs. path' v xs v')"
    apply auto by (simp add: rtrancl_is_path' path'_is_rtrancl)+

  (** These lemmas show that paths are a subset of the graph *)
  lemma epath_subset: "epath v es v' \<Longrightarrow> set es \<subseteq> E"
    using split_list by fastforce

  lemma path_subset: "path v xs v' \<Longrightarrow> set xs \<subseteq> V"
  unfolding V_def
  proof (induction xs arbitrary: v)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    hence "(v,a) \<in> E" by simp
    hence "a \<in> snd ` E" by force
    with Cons show ?case by auto
  qed

  lemma path'_subset: "path' v xs v' \<Longrightarrow> set xs \<subseteq> V"
  unfolding V_def
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
    apply (induction xs arbitrary: v) apply auto by fastforce

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

  definition cycle_from_node :: "'v \<Rightarrow> 'v list \<Rightarrow> bool" where
    "cycle_from_node v xs \<equiv> \<exists>v'. (v,v')\<in>E\<^sup>* \<and> cycle_node v' xs"

  lemma lasso_comp: "path' u xs v \<Longrightarrow> cycle_node v ys \<Longrightarrow> cycle_from_node u ys"
    unfolding cycle_from_node_def using path'_is_rtrancl by blast

  lemma lasso_decomp: "cycle_from_node u ys \<Longrightarrow> \<exists>xs v. cycle_node v ys \<and> path' u xs v"
    unfolding cycle_from_node_def using rtrancl_is_path' by blast

  definition lasso_from_node :: "'v \<Rightarrow> 'v list \<Rightarrow> 'v list \<Rightarrow> bool" where
    "lasso_from_node v xs ys \<equiv> \<exists>v'. path' v xs v' \<and> path' v' ys v' \<and> ys \<noteq> []"

  lemma lasso_from_equiv_cycle_from: "(\<exists>xs. lasso_from_node v xs ys) \<longleftrightarrow> cycle_from_node v ys"
    unfolding lasso_from_node_def cycle_from_node_def cycle_node_def
  proof
    assume "\<exists>xs v'. path' v xs v' \<and> path' v' ys v' \<and> ys \<noteq> []"
    then show "\<exists>v'. (v,v') \<in> E\<^sup>* \<and> path' v' ys v' \<and> ys \<noteq> []"
      using path'_is_rtrancl by auto
  next
    assume "\<exists>v'. (v,v') \<in> E\<^sup>* \<and> path' v' ys v' \<and> ys \<noteq> []"
    then show "\<exists>xs v'. local.path' v xs v' \<and> local.path' v' ys v' \<and> ys \<noteq> []"
      using path'_equiv_rtrancl by auto
  qed

  lemma path_any_length: "finite E \<Longrightarrow> \<forall>v. E``{v} \<noteq> {} \<Longrightarrow> \<exists>xs v'. length xs = n \<and> path' v xs v'"
  proof (induction n)
    case 0
    then obtain xs v' where "xs=([]::'v list)" and "v' = v" by simp
    then show ?case by auto
  next
    case (Suc n)
    then obtain xs v' w
      where path: "length xs = n \<and> path' v xs v'"
      and succ: "w \<in> E``{v'}" by fast
    then obtain ys where append: "ys = xs@[v']" by fast
    with path have length: "length ys = Suc n" by simp
    from append path succ have "path' v ys w" by auto
    with length show ?case by auto
  qed

  lemma finite_graph_lasso:  "finite E \<Longrightarrow> \<forall>v. E``{v} \<noteq> {} \<Longrightarrow> \<exists>x xs. cycle_from_node x xs"
  proof -
    assume fin: "finite E" and succ: "\<forall>v. E``{v} \<noteq> {}"
    then obtain v xs v' where xs: "length (xs::'v list) = (card V) + 1 \<and> path' v xs v'"
      using path_any_length by blast
    have "\<not>distinct xs" proof -
      from xs have "set xs \<subseteq> V" using path'_subset by auto
      moreover from xs have "length xs > card V" by auto
      moreover from fin have "finite V" unfolding V_def by simp
      ultimately show ?thesis by (simp add: finite_subset_not_distinct)
    qed
    hence "\<exists>x xs1 xs2 xs3. xs = xs1 @ [x] @ xs2 @ [x] @ xs3" using not_distinct_decomp by blast
    then obtain x xs1 xs2 xs3 where decomp: "xs = xs1 @ [x] @ xs2 @ [x] @ xs3" by blast
    with xs have "path' v (xs1) x" using path'_decomp_1 by blast
    moreover from decomp xs have "path' x (x#xs2) x" using path'_decomp_2 by blast
    hence "cycle_node x (x#xs2)" by (simp add: cycle_node_def)
    ultimately have "cycle_from_node v (x#xs2)" using lasso_comp by simp
    then show ?thesis by auto
  qed

  lemma finite_graph_lasso_always:  "finite E \<Longrightarrow> \<forall>v. E``{v} \<noteq> {} \<Longrightarrow> \<forall>x. \<exists>xs. cycle_from_node x xs"
  proof auto
    fix x
    assume fin: "finite E" and succ: "\<forall>v. E``{v} \<noteq> {}"
    then obtain xs x' where xs: "length (xs::'v list) = (card V) + 1 \<and> path' x xs x'"
      using path_any_length by blast
    have "\<not>distinct xs" proof -
      from xs have "set xs \<subseteq> V" using path'_subset by auto
      moreover from xs have "length xs > card V" by auto
      moreover from fin have "finite V" unfolding V_def by simp
      ultimately show ?thesis by (simp add: finite_subset_not_distinct)
    qed
    hence "\<exists>y xs1 xs2 xs3. xs = xs1 @ [y] @ xs2 @ [y] @ xs3" using not_distinct_decomp by blast
    then obtain y xs1 xs2 xs3 where decomp: "xs = xs1 @ [y] @ xs2 @ [y] @ xs3" by blast
    with xs have "path' x (xs1) y" using path'_decomp_1 by blast
    moreover from decomp xs have "path' y (y#xs2) y" using path'_decomp_2 by blast
    hence "cycle_node y (y#xs2)" by (simp add: cycle_node_def)
    ultimately have "cycle_from_node x (y#xs2)" using lasso_comp by blast
    then show "\<exists>xs. cycle_from_node x xs" by auto
  qed
end

subsection \<open>Paths in Subgraphs\<close>
lemma subgraph_path: "E' \<subseteq> E \<Longrightarrow> path' E' v vs v' \<Longrightarrow> path' E v vs v'"
  apply (induction vs arbitrary: v) by auto

lemma subgraph_cycle: "E' \<subseteq> E \<Longrightarrow> cycle_node E' v vs \<Longrightarrow> cycle_node E v vs"
  unfolding cycle_node_def
  apply (induction vs arbitrary: v)
  by (auto simp: subgraph_path)

lemma subgraph_lasso: "E' \<subseteq> E \<Longrightarrow> cycle_from_node E' v vs \<Longrightarrow> cycle_from_node E v vs"
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

lemma lasso_inter_1: "cycle_from_node (E1 \<inter> E2) v vs \<Longrightarrow> cycle_from_node E1 v vs"
  proof -
    assume "cycle_from_node (E1 \<inter> E2) v vs"
    moreover have "(E1 \<inter> E2) \<subseteq> E1" by fast
    ultimately show "cycle_from_node E1 v vs" using subgraph_lasso by metis
  qed

lemma lasso_inter_2: "cycle_from_node (E1 \<inter> E2) v vs \<Longrightarrow> cycle_from_node E2 v vs"
  proof -
    assume "cycle_from_node (E1 \<inter> E2) v vs"
    moreover have "(E1 \<inter> E2) \<subseteq> E2" by fast
    ultimately show "cycle_from_node E2 v vs" using subgraph_lasso by metis
  qed

subsection \<open>Winning Strategies\<close>

locale arena_defs =
  fixes E :: "'v dgraph"
  fixes V\<^sub>0 :: "'v set"
  fixes prio :: "'v \<Rightarrow> nat"
  assumes fin: "finite E"
  assumes succ: "E``{v} \<noteq> {}"
begin  
  definition V where "V = fst`E \<union> snd`E"
  definition V\<^sub>1 where "V\<^sub>1 = V-V\<^sub>0"

  lemma V_universe[simp]: "V=UNIV"
    unfolding V_def using succ by force
  
  lemma players_disjoint: "V\<^sub>0 \<inter> V\<^sub>1 = {}"
    unfolding V_def V\<^sub>1_def by auto

  lemma in_V\<^sub>1_notin_V\<^sub>0: "v\<notin>V\<^sub>0 \<longleftrightarrow> v\<in>V\<^sub>1"
    unfolding V\<^sub>1_def by simp

  text \<open>A positional strategy for a player i is a function \<sigma>:Vi\<rightarrow>V\<close>
  type_synonym 'a strat = "'a \<Rightarrow> 'a option"

  definition E_of_strat :: "'a strat \<Rightarrow> 'a dgraph" where
    "E_of_strat \<sigma> = {(u,v). \<sigma> u = Some v}"

  definition top_priority :: "'v list \<Rightarrow> nat" where
    "top_priority xs \<equiv> MAX v \<in> set xs. prio v"

  abbreviation winning_even :: "'v list \<Rightarrow> bool" where
    "winning_even xs \<equiv> even (top_priority xs)"

  abbreviation winning_odd :: "'v list \<Rightarrow> bool" where
    "winning_odd xs \<equiv> odd (top_priority xs)"

  definition strategy_of :: "'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
    "strategy_of S \<sigma> \<equiv> dom \<sigma> \<subseteq> S \<and> E_of_strat \<sigma> \<subseteq> E"

  lemma strats_disjoint: "\<forall>\<sigma> \<tau>. strategy_of V\<^sub>0 \<sigma> \<and> strategy_of V\<^sub>1 \<tau> \<longrightarrow> (dom \<sigma> \<inter> dom \<tau>) = {}"
    unfolding strategy_of_def using players_disjoint by blast

  definition induced_by_strategy :: "'v strat \<Rightarrow> 'v dgraph" where
    "induced_by_strategy \<sigma> = E \<inter> ((-dom \<sigma>) \<times> UNIV \<union> E_of_strat \<sigma>)"

  lemma ind_subgraph: "induced_by_strategy \<sigma> \<subseteq> E"
    unfolding induced_by_strategy_def by auto

  lemma ind_subgraph_finite: "finite (induced_by_strategy \<sigma>)"
    using ind_subgraph fin finite_subset by blast

  lemma ind_subgraph_cycle: "cycle_node (induced_by_strategy \<sigma>) v xs \<Longrightarrow> cycle_node E v xs"
  proof -
    assume 0: "cycle_node (induced_by_strategy \<sigma>) v xs"
    from ind_subgraph have 1: "induced_by_strategy \<sigma> \<subseteq> E" by simp
    hence "cycle_node (induced_by_strategy \<sigma>) v xs \<Longrightarrow> cycle_node E v xs"
      by (simp add:subgraph_cycle)
    with 0 1 show ?thesis by simp
  qed

  lemma ind_subgraph_lasso: "cycle_from_node (induced_by_strategy \<sigma>) v xs \<Longrightarrow> cycle_from_node E v xs"
  proof -
    assume 0: "cycle_from_node (induced_by_strategy \<sigma>) v xs"
    from ind_subgraph have 1: "induced_by_strategy \<sigma> \<subseteq> E" by simp
    hence "cycle_from_node (induced_by_strategy \<sigma>) v xs \<Longrightarrow> cycle_from_node E v xs"
      by (simp add:subgraph_lasso)
    with 0 1 show ?thesis by simp
  qed

  inductive attr_even :: "'v set \<Rightarrow> 'v set \<Rightarrow> bool" for X where
  base: "attr_even X X" |
  step: "attr_even X Y \<Longrightarrow> Y' = Y \<union> {v|v. v\<in>V\<^sub>0 \<and>  E``{v} \<inter> Y \<noteq> {}} \<union> {v|v. v\<in>V\<^sub>1 \<and> E``{v} \<subseteq> Y} \<Longrightarrow>  attr_even X Y'"

lemma "attr_even X Y \<Longrightarrow> \<forall>y\<in>Y. \<exists>\<sigma>. strategy_of V\<^sub>0 \<sigma> \<and> (\<forall>xs ys. lasso_from_node (induced_by_strategy \<sigma>) y xs ys \<longrightarrow>
        (X \<subseteq> set xs \<or> X \<subseteq> set ys))"
  proof (induction rule: attr_even.induct)
    case base
    then show ?case sorry
  next
    case (step Y Y')
    then show ?case sorry
  qed
  
  definition won_by_even :: "'v \<Rightarrow> bool" where
    "won_by_even v \<equiv> \<exists>\<sigma>. strategy_of V\<^sub>0 \<sigma> \<and> 
    (\<forall>xs. cycle_from_node (induced_by_strategy \<sigma>) v xs \<longrightarrow> winning_even xs)"

  lemma "won_by_even v \<Longrightarrow> \<exists>\<sigma>. strategy_of V\<^sub>0 \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy \<sigma>) v xs \<longrightarrow> \<not>winning_odd xs)"
    unfolding won_by_even_def by auto

  definition won_by_odd :: "'v \<Rightarrow> bool" where
    "won_by_odd v \<equiv> \<exists>\<sigma>. strategy_of V\<^sub>1 \<sigma> \<and> 
    (\<forall>xs. cycle_from_node (induced_by_strategy \<sigma>) v xs \<longrightarrow> winning_odd xs)"

  lemma "won_by_odd v \<Longrightarrow> \<exists>\<sigma>. strategy_of V\<^sub>1 \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy \<sigma>) v xs \<longrightarrow> \<not>winning_even xs)"
    unfolding won_by_odd_def by auto

  lemma V\<^sub>0_induced_succs_1: "v\<in>V\<^sub>0 \<Longrightarrow> strategy_of V\<^sub>1 \<sigma>' \<Longrightarrow> induced_by_strategy \<sigma>' `` {v} = E `` {v}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def V\<^sub>1_def by auto
  
  lemma V\<^sub>0_induced_succs_2: "v\<in>V\<^sub>0 \<Longrightarrow> strategy_of V\<^sub>0 \<sigma> \<Longrightarrow> induced_by_strategy \<sigma> `` {v} \<noteq> {}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def V\<^sub>1_def
    using succ[of v] apply (cases "v\<in>dom \<sigma>") by auto
  
  lemma V\<^sub>1_induced_succs_1: "v\<in>V\<^sub>1 \<Longrightarrow> strategy_of V\<^sub>0 \<sigma>' \<Longrightarrow> induced_by_strategy \<sigma>' `` {v} = E `` {v}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def V\<^sub>1_def by auto
  
  lemma V\<^sub>1_induced_succs_2: "v\<in>V\<^sub>1 \<Longrightarrow> strategy_of V\<^sub>1 \<sigma> \<Longrightarrow> induced_by_strategy \<sigma> `` {v} \<noteq> {}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def V\<^sub>1_def
    using succ[of v] apply (cases "v\<in>dom \<sigma>") by auto

  lemma w1: "won_by_even v \<Longrightarrow> \<not>won_by_odd v"
    unfolding won_by_even_def won_by_odd_def
  proof clarsimp
    fix \<sigma> \<sigma>'
    define G\<sigma> where "G\<sigma> = induced_by_strategy \<sigma>"
    define G\<sigma>' where "G\<sigma>' = induced_by_strategy \<sigma>'"
    assume \<sigma>_even: "strategy_of V\<^sub>0 \<sigma>"
      and \<sigma>_win: "\<forall>xs. cycle_from_node G\<sigma> v xs \<longrightarrow> even (top_priority xs)"
      and \<sigma>'_odd: "strategy_of V\<^sub>1 \<sigma>'"
    interpret Ginter: arena_defs "G\<sigma> \<inter> G\<sigma>'" V\<^sub>0 prio 
      apply unfold_locales
      subgoal  unfolding G\<sigma>_def by (auto simp: ind_subgraph_finite)
      proof cases
        fix v
        assume v_in_V\<^sub>0: "v\<in>V\<^sub>0"
        with \<sigma>'_odd have "G\<sigma>' `` {v} = E `` {v}"
          unfolding G\<sigma>'_def by (simp add: V\<^sub>0_induced_succs_1)
        moreover from v_in_V\<^sub>0 \<sigma>_even  have "G\<sigma> `` {v} \<noteq> {}"
          unfolding G\<sigma>_def by (simp add: V\<^sub>0_induced_succs_2)
        moreover note succ[of v] 
        moreover have "G\<sigma> \<subseteq> E" by (simp add: G\<sigma>_def ind_subgraph)
        ultimately show "(G\<sigma> \<inter> G\<sigma>') `` {v} \<noteq> {}" by fast
      next
        fix v
        assume "v\<notin>V\<^sub>0"
        hence v_in_V\<^sub>1: "v\<in>V\<^sub>1" by (simp add: in_V\<^sub>1_notin_V\<^sub>0)
        with \<sigma>_even have "G\<sigma> `` {v} = E `` {v}"
          unfolding G\<sigma>_def by (simp add: V\<^sub>1_induced_succs_1)
        moreover from v_in_V\<^sub>1 \<sigma>'_odd have "G\<sigma>' `` {v} \<noteq> {}"
          unfolding G\<sigma>'_def by (simp add: V\<^sub>1_induced_succs_2)
        moreover note succ[of v] 
        moreover have "G\<sigma>' \<subseteq> E" by (simp add: G\<sigma>'_def ind_subgraph)
        ultimately show "(G\<sigma> \<inter> G\<sigma>') `` {v} \<noteq> {}" by fast
      qed
    from finite_graph_lasso_always[OF Ginter.fin] Ginter.succ
    obtain xs where xs: "cycle_from_node (G\<sigma> \<inter> G\<sigma>') v xs" by blast
    moreover from xs have "cycle_from_node G\<sigma>' v xs" using lasso_inter_2 by fastforce
    moreover from xs have "cycle_from_node G\<sigma> v xs" using lasso_inter_1 by fastforce
    with \<sigma>_win have "even (top_priority xs)" by blast
    ultimately show "\<exists>xs. cycle_from_node (G\<sigma>') v xs \<and> even (top_priority xs)" by blast
  qed

  lemma w': "\<not>won_by_odd v \<Longrightarrow> won_by_even v" unfolding won_by_odd_def won_by_even_def apply clarsimp
  apply (drule spec[where x=\<sigma>1]) apply (subgoal_tac "strategy_of V\<^sub>1 \<sigma>1") apply clarsimp sorry

  lemma w2:"won_by_even v \<or> won_by_odd v" sorry
  
  lemma "won_by_even v \<noteq> won_by_odd v" using w1 w' by blast

end

subsection \<open>Miscellaneous\<close>

text \<open>
  A strategy for player i is a function \<sigma>:V*Vi\<rightarrow>V that selects a successor for every history of the
  play ending in a vertex of player i.
  A strategy is memoryless iff \<sigma>(wv) = \<sigma>(v) for all w\<in>V*, v\<in>Vi.
  A strategy is winning from a vertex v if all plays starting in v and consistent with \<sigma> are winning
  for player i.
\<close>

locale arena = arena_defs E V\<^sub>0 
  for  
    E :: "'v dgraph"
  and V\<^sub>0 :: "'v set"  
  + 
  assumes V0_ss: "V\<^sub>0 \<subseteq> V"
  assumes succ: "E``{v}\<noteq>{}"
  assumes fin: "finite (UNIV::'v set)"
begin

text \<open>Wholly unnecessary but allows me to not have to unfold V1_def all the time.\<close>
lemma V1_ss[simp]: "V\<^sub>1 \<subseteq> V"
  unfolding V\<^sub>1_def by auto

definition connected where "connected v v' \<longleftrightarrow> (v,v')\<in>E\<^sup>*"
  
lemma conn: "v\<in>V \<Longrightarrow> connected v v' \<Longrightarrow> v'\<in>V"
  unfolding connected_def V_def
  by (metis Range.RangeI Range_snd UnCI rtranclE)
end
  
end
