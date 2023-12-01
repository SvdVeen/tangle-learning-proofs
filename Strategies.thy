theory Strategies
  imports Main Digraphs
begin

chapter \<open>Arenas and Strategies\<close>

section \<open>Arenas\<close>
(** An arena is a finite directed graph without dead ends, along with sets of vertices that belong
    to either player. We can get by with only specifying the even player's nodes, and getting the
    odd player's nodes by subtracting the even player's nodes from the set of all nodes *)
locale arena = finite_graph_V_Succ +
  fixes V\<^sub>0 :: "'v set"
  assumes V\<^sub>0_in_V: "V\<^sub>0 \<subseteq> V"
begin

(** The odd player's nodes are all nodes in V that are not in V\<^sub>1 *)
definition V\<^sub>1 where "V\<^sub>1 = V - V\<^sub>0"

(** V\<^sub>1 is a subset of V *)
lemma V\<^sub>1_in_V: "V\<^sub>1 \<subseteq> V"
  unfolding V\<^sub>1_def using V\<^sub>0_in_V by blast

(** V\<^sub>0 is the opposite of V\<^sub>1 because it is V\<^sub>1 subtracted from V *)
lemma V\<^sub>0_opposite_V\<^sub>1: "V\<^sub>0 = V - V\<^sub>1"
  unfolding V\<^sub>1_def using V\<^sub>0_in_V by auto

(** There is no overlap between the two players' nodes *)
lemma players_disjoint: "V\<^sub>0 \<inter> V\<^sub>1 = {}"
  unfolding V\<^sub>1_def by auto

(** If a node is in V\<^sub>0, it is not in V\<^sub>1 and vice versa *)
lemma in_V\<^sub>1_notin_V\<^sub>0: "v\<in>V \<Longrightarrow> v\<notin>V\<^sub>0 \<longleftrightarrow> v\<in>V\<^sub>1"
  unfolding V\<^sub>1_def by blast


section \<open>Strategies\<close>
(** A positional strategy for a player \<alpha> is a function \<sigma>:V\<^sub>\<alpha>\<rightarrow>V *)
type_synonym 'a strat = "'a \<Rightarrow> 'a option"


subsection \<open>Edges of a Strategy\<close>
(** The set of edges in a strategy *)
definition E_of_strat :: "'a strat \<Rightarrow> 'a dgraph" where
  "E_of_strat \<sigma> = {(u,v). \<sigma> u = Some v}"

lemma E_of_strat_empty[simp]: "E_of_strat Map.empty = {}"
  unfolding E_of_strat_def by fast

lemma E_of_strat_empty_iff_empty_map[simp]: "E_of_strat \<sigma> = {} \<longleftrightarrow> \<sigma> = Map.empty"
  unfolding E_of_strat_def by auto

(** If a strategy is part of another, its edges are a subset of the other strategy's edges *)
lemma strat_le_E_of_strat: "\<sigma> \<subseteq>\<^sub>m \<sigma>' \<Longrightarrow> E_of_strat \<sigma> \<subseteq> E_of_strat \<sigma>'"
  unfolding map_le_def E_of_strat_def by force

(** If the strategy leads to a w for some v, then (v,w) is an edge in the strategy *)
lemma edge_in_E_of_strat: "\<sigma> v = Some w \<longleftrightarrow> (v,w) \<in> E_of_strat \<sigma>"
  unfolding E_of_strat_def by simp

(** The domain of a strategy is equal to all source nodes in its edges *)
lemma E_of_strat_dom: "dom \<sigma> = fst`E_of_strat \<sigma>"
  unfolding E_of_strat_def by force

(** The range of a strategy is equal to all target nodes in its edges *)
lemma E_of_strat_ran: "ran \<sigma> = snd`E_of_strat \<sigma>"
  unfolding E_of_strat_def ran_def by force


subsection \<open>Strategies of Sets\<close>
(** Checks whether a strategy is in the graph and belongs to a particular player *)
definition strategy_of :: "'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "strategy_of S \<sigma> \<equiv> dom \<sigma> \<subseteq> S \<and> E_of_strat \<sigma> \<subseteq> E"

lemma strategy_of_empty[simp]: "strategy_of S Map.empty"
  unfolding strategy_of_def by auto

lemma strategy_of_empty_iff_empty_strategy[simp]: "strategy_of {} \<sigma> \<longleftrightarrow> \<sigma> = Map.empty"
  unfolding strategy_of_def by auto

(** If \<sigma> is a strategy of S, its domain is a subset of S *)
lemma strategy_of_dom: "strategy_of S \<sigma> \<Longrightarrow> dom \<sigma> \<subseteq> S"
  unfolding strategy_of_def by simp

(** If \<sigma> is a strategy of S, all of its edges are in the graph *)
lemma strategy_of_in_E: "strategy_of S \<sigma> \<Longrightarrow> E_of_strat \<sigma> \<subseteq> E"
  unfolding strategy_of_def by simp

(** A single mapping is a strategy of S if what it maps exists and the source is in S *)
lemma strategy_of_map_assign: "\<lbrakk>x\<in>S; (x,y)\<in>E\<rbrakk> \<Longrightarrow> strategy_of S [x\<mapsto>y]"
  unfolding strategy_of_def E_of_strat_def
  by (auto split: if_splits)

(** Adding two strategies of some S creates a strategy of that S *)
lemma strategy_of_add_same[simp]: "\<lbrakk>strategy_of S \<sigma>; strategy_of S \<sigma>'\<rbrakk> \<Longrightarrow> strategy_of S (\<sigma> ++ \<sigma>')"
  unfolding strategy_of_def E_of_strat_def by auto

(** If all edges of a strategy exist in E, it is also a strategy of its own domain *)
lemma strategy_of_own_dom: "E_of_strat \<sigma> \<subseteq> E \<Longrightarrow>  strategy_of (dom \<sigma>) \<sigma>"
  unfolding strategy_of_def by blast


subsection \<open>Induced Subgraphs\<close>
(** The induced subgraph of a strategy *)
definition induced_subgraph :: "'v set \<Rightarrow> 'v strat \<Rightarrow> 'v dgraph" where
  "induced_subgraph V\<^sub>\<alpha> \<sigma> = E \<inter> ((-V\<^sub>\<alpha>) \<times> UNIV \<union> E_of_strat \<sigma>)"

lemma ind_subgraph_empty[simp]: "induced_subgraph V\<^sub>\<alpha> Map.empty = E \<inter> (-V\<^sub>\<alpha>) \<times> UNIV"
  unfolding induced_subgraph_def by simp
lemma ind_subgraph_empty'[simp]: "induced_subgraph (dom Map.empty) Map.empty = E" by simp

(** The induced subgraph is a subgraph of the whole graph *)
lemma ind_subgraph[simp]: "induced_subgraph V\<^sub>\<alpha> \<sigma> \<subseteq> E"
  unfolding induced_subgraph_def by auto
lemma ind_subgraph_edge_in_E[simp]: "(v,w) \<in> induced_subgraph V\<^sub>\<alpha> \<sigma> \<Longrightarrow> (v,w) \<in> E"
  using ind_subgraph by blast

(** Induced subgraphs are finite *)
lemma ind_subgraph_finite[simp]: "finite (induced_subgraph V\<^sub>\<alpha> \<sigma>)"
  using ind_subgraph fin_E finite_subset by blast

(** A more specific simplification of the induced subgraph definition *)
lemma ind_subgraph_in_V: "induced_subgraph V\<^sub>\<alpha> \<sigma> = E \<inter> ((V-V\<^sub>\<alpha>) \<times> V \<union> E_of_strat \<sigma>)"
  unfolding induced_subgraph_def using E_in_V by blast

(** The induced subgraph with some domain is a subset of the induced subgraph with a subset of
    that domain *)
lemma ind_subgraph_anti_mono: "V\<^sub>\<alpha> \<subseteq> V\<^sub>\<alpha>' \<Longrightarrow> induced_subgraph V\<^sub>\<alpha>' \<sigma> \<subseteq> induced_subgraph V\<^sub>\<alpha> \<sigma>"
  unfolding induced_subgraph_def by auto

(** The induced subgraph of some subset of a strategy is a subset of the induced subgraph of that
    strategy *)
lemma ind_subgraph_strategy_mono: "\<lbrakk>\<sigma> \<subseteq>\<^sub>m \<sigma>'; dom \<sigma>' \<subseteq> V\<^sub>\<alpha>\<rbrakk> \<Longrightarrow> induced_subgraph V\<^sub>\<alpha> \<sigma> \<subseteq> induced_subgraph V\<^sub>\<alpha> \<sigma>'"
  unfolding induced_subgraph_def E_of_strat_def map_le_def by force

(** If an edge exists in the graph and its source is not in the domain of \<sigma>, it exists in the
    induced subgraph of \<sigma> *)
lemma ind_subgraph_notin_dom: "\<lbrakk>(v,w) \<in> E; v \<notin> V\<^sub>\<alpha>\<rbrakk> \<Longrightarrow> (v,w) \<in> induced_subgraph V\<^sub>\<alpha> \<sigma>"
  unfolding induced_subgraph_def by simp

(** The successors of all nodes outside the induced subgraph's domain are the same as their
    successors in the full graph *)
lemma ind_subgrah_notin_dom_succs: "induced_subgraph V\<^sub>\<alpha> \<sigma> `` (-V\<^sub>\<alpha>) = E `` (-V\<^sub>\<alpha>)"
  unfolding induced_subgraph_def by blast

(** If an edge exists in the induced subgraph of \<sigma>, it is either in the domain of \<sigma> or not *)
lemma ind_subgraph_edge_src: "(v,w) \<in> induced_subgraph V\<^sub>\<alpha> \<sigma> \<Longrightarrow> v \<in> dom \<sigma> \<or> v \<in> (-V\<^sub>\<alpha>)"
  unfolding induced_subgraph_def E_of_strat_def by auto

(** If an edge exists in the induced subgraph of \<sigma> and it is in the domain, its destination is
    in the range of \<sigma> *)
lemma ind_subgraph_edge_dst: "\<lbrakk>(v,w) \<in> induced_subgraph V\<^sub>\<alpha> \<sigma>; v \<in> V\<^sub>\<alpha>\<rbrakk> \<Longrightarrow> w \<in> ran \<sigma>"
  unfolding induced_subgraph_def E_of_strat_def ran_def by blast

(** An induced subgraph in a closed region with a range into that region is closed in that
    region *)
lemma ind_subgraph_closed_region:
  "\<lbrakk>R\<subseteq>V; E `` (R \<inter> (V-V\<^sub>\<alpha>)) \<subseteq> R; ran \<sigma> \<subseteq> R\<rbrakk> \<Longrightarrow> induced_subgraph V\<^sub>\<alpha> \<sigma> `` R \<subseteq> R"
  using ind_subgraph_edge_dst ind_subgraph_edge_in_E by blast

(** If an edge is in an induced subgraph and its source is in the domain, the strategy maps its
    source to its target *)
lemma ind_subgraph_to_strategy: "\<lbrakk>(v, w) \<in> induced_subgraph V\<^sub>\<alpha> \<sigma>; v \<in> V\<^sub>\<alpha>\<rbrakk> \<Longrightarrow> \<sigma> v = Some w"
  unfolding induced_subgraph_def E_of_strat_def by blast

(** If a strategy maps a node to another, and that edge exists in the graph, it also exists in
    the induced subgraph *)
lemma strategy_to_ind_subgraph: "\<lbrakk>\<sigma> v = Some w; (v,w) \<in> E \<rbrakk> \<Longrightarrow> (v,w) \<in> induced_subgraph V\<^sub>\<alpha> \<sigma>"
  unfolding induced_subgraph_def E_of_strat_def by auto

(** If you add two disjoint strategies, their combined induced subgraph is a subset of either of
    their induced subgraphs *)
lemma ind_subgraph_add_disjoint:
  "dom \<sigma> \<inter> dom \<sigma>' = {} \<Longrightarrow> induced_subgraph (dom (\<sigma> ++ \<sigma>')) (\<sigma> ++ \<sigma>') \<subseteq>
    induced_subgraph (dom \<sigma>) \<sigma>"
  "dom \<sigma> \<inter> dom \<sigma>' = {} \<Longrightarrow> induced_subgraph (dom (\<sigma> ++ \<sigma>')) (\<sigma> ++ \<sigma>') \<subseteq>
    induced_subgraph (dom \<sigma>') \<sigma>'"
  unfolding induced_subgraph_def E_of_strat_def by auto

(** If you add two strategies, any edge that does not start in one of their domains exists in
    the induced subgraph of the other strategy *)
lemma ind_subgraph_add_notin_dom:
  "\<lbrakk>(v,v')\<in>induced_subgraph (dom (\<sigma> ++ \<sigma>')) (\<sigma> ++ \<sigma>'); v \<notin> dom \<sigma>'\<rbrakk>
    \<Longrightarrow> (v,v') \<in> induced_subgraph (dom \<sigma>) \<sigma>"
  "\<lbrakk>(v,v')\<in>induced_subgraph (dom (\<sigma> ++ \<sigma>')) (\<sigma> ++ \<sigma>'); v \<notin> dom \<sigma>\<rbrakk>
    \<Longrightarrow> (v,v') \<in> induced_subgraph (dom \<sigma>') \<sigma>'"
  unfolding induced_subgraph_def E_of_strat_def
  using map_add_dom_app_simps by auto

(** Paths that exist in an induced subgraph also exist in the whole graph. Shorthand for an
    existing combination of lemmas *)
lemma ind_subgraph_path: "path (induced_subgraph V\<^sub>\<alpha> \<sigma>) v xs v' \<Longrightarrow> path E v xs v'"
  using subgraph_path[OF ind_subgraph] .

(** Cycles that exist in an induced subgraph also exist in the whole graph. Shorthand for an
    existing combination of lemmas *)
lemma ind_subgraph_cycle: "cycle (induced_subgraph V\<^sub>\<alpha> \<sigma>) v xs \<Longrightarrow> cycle E v xs"
  using subgraph_cycle[OF ind_subgraph] .

lemma ind_subgraph_cycle_from_node: "cycle_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) v xs
   \<Longrightarrow> cycle_from_node E v xs"
  using subgraph_cycle_from_node[OF ind_subgraph] .

(** Lassos that exist in and induced subgraph also exist in the whole graph. Shorthand for an
    existing combination of lemmas *)
lemma ind_subgraph_lasso: "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
  \<Longrightarrow> lasso_from_node E x xs ys"
  using subgraph_lasso[OF ind_subgraph] .

lemma ind_subgraph_lasso': "lasso_from_node' (induced_subgraph V\<^sub>\<alpha> \<sigma>) v xs
  \<Longrightarrow> lasso_from_node' E v xs"
  using subgraph_lasso'[OF ind_subgraph] .


subsection \<open>Nodes in an Induced Subgraph\<close>
(** The set of all nodes in an induced subgraph *)
definition induced_subgraph_V :: "'v set \<Rightarrow> 'v strat \<Rightarrow> 'v set" where
  "induced_subgraph_V V\<^sub>\<alpha> \<sigma> \<equiv> (fst ` induced_subgraph V\<^sub>\<alpha> \<sigma> \<union> snd ` induced_subgraph V\<^sub>\<alpha> \<sigma>)"

(** The nodes in an induced subgraph are a subset of V *)
lemma ind_subgraph_V_in_V[simp]: "induced_subgraph_V V\<^sub>\<alpha> \<sigma> \<subseteq> V"
  unfolding induced_subgraph_V_def
  using ind_subgraph E_in_V by fastforce

(** The set of nodes in an induced subgraph is finite *)
lemma ind_subgraph_V_finite[simp]: "finite (induced_subgraph_V V\<^sub>\<alpha> \<sigma>)"
  using finite_subset[OF ind_subgraph_V_in_V fin_V] by simp


subsection \<open>Induced Subgraphs in Subarenas\<close>
(** All nodes in an induced subgraph still have a successor *)
lemma ind_subgraph_succ: "\<lbrakk>v \<in> induced_subgraph_V (dom \<sigma>) \<sigma>; E_of_strat \<sigma> \<subseteq> E\<rbrakk>
  \<Longrightarrow> induced_subgraph (dom \<sigma>) \<sigma> `` {v} \<noteq> {}"
  apply (cases "v \<in> dom \<sigma>")
    subgoal using edge_in_E_of_strat[of \<sigma>] strategy_to_ind_subgraph by blast
    subgoal using ind_subgraph_notin_dom[of v _ "dom \<sigma>"] succ ind_subgraph_V_in_V by blast
    done

(** An induced subgraph is still a valid finite graph *)
lemma ind_subgraph_is_finite_graph[simp]:
  "finite_graph_V (induced_subgraph V\<^sub>\<alpha> \<sigma>) (induced_subgraph_V V\<^sub>\<alpha> \<sigma>)"
  apply (unfold_locales)
    subgoal unfolding induced_subgraph_V_def by force
    subgoal by simp
  done

(** An induced subgraph is still a valid finite graph without dead ends *)
lemma ind_subgraph_is_finite_graph_succ: "E_of_strat \<sigma> \<subseteq> E
  \<Longrightarrow> finite_graph_V_Succ (induced_subgraph (dom \<sigma>) \<sigma>) (induced_subgraph_V (dom \<sigma>) \<sigma>)"
  apply (unfold_locales)
    subgoal unfolding induced_subgraph_V_def by force
    subgoal by simp
    subgoal using ind_subgraph_succ by simp
  done

(** Restricting an induced subgraph to the edges of a subarena means it is a subset of the same
    induced subgraph in that subarena *)
lemma ind_subgraph_restr_subarena:
  assumes "arena E' V' V\<^sub>0'"
  assumes "V\<^sub>\<alpha>' \<subseteq> V\<^sub>\<alpha>"
  shows "induced_subgraph V\<^sub>\<alpha> \<sigma> \<inter> E' \<subseteq> arena.induced_subgraph E' V\<^sub>\<alpha>' \<sigma>"
  unfolding induced_subgraph_def arena.induced_subgraph_def[OF assms(1)] E_of_strat_def
  using assms(2) by auto


subsubsection \<open>Restricted Subgraphs\<close>
lemma restr_ind_subgraph:
  assumes "arena (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"
  shows "arena.induced_subgraph (Restr E R) V\<^sub>\<alpha> \<sigma> = Restr (induced_subgraph V\<^sub>\<alpha> \<sigma>) R"
  unfolding arena.induced_subgraph_def[OF assms] induced_subgraph_def
  by auto

lemma restr_ind_subgraph_V\<^sub>\<alpha>:
  assumes "arena (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"
  shows "arena.induced_subgraph (Restr E R) (V\<^sub>\<alpha> \<inter> R) \<sigma> = Restr (induced_subgraph V\<^sub>\<alpha> \<sigma>) R"
  unfolding arena.induced_subgraph_def[OF assms] induced_subgraph_def
  by auto
end (** End of locale arena *)

end
