theory TangleLearning
imports Main ParityGames
begin
chapter \<open>Tangle Learning\<close>
section \<open>Tangle Definitions\<close>

context paritygame begin
(** There must be a nicer way to define this using contexts or locales *)
definition p_tangle :: "nat \<Rightarrow> 'v set \<Rightarrow> bool" where
  "p_tangle p U \<equiv> U \<noteq> {} \<and> U \<subseteq> V \<and> p = Max (prio ` U) \<and> (\<exists>\<sigma>.
   strategy_of (U \<inter> V_player (player_wins_prio p)) \<sigma> \<and> ran \<sigma> \<subseteq> U \<and>
   strongly_connected (E \<inter> (((U \<inter> V_opponent (player_wins_prio p)) \<times> U) \<union> E_of_strat \<sigma>)) \<and>
   (\<forall>v \<in> U \<inter> V_player (player_wins_prio p). \<forall>ys. cycle_from_node (E \<inter> (((U \<inter> V_opponent (player_wins_prio p)) \<times> U) \<union> E_of_strat \<sigma>)) v ys
   \<longrightarrow> player_winningP (player_wins_prio p) (top_priority ys)))"

context
  fixes U :: "'v set"
  assumes ne: "U \<noteq> {}"
  assumes ss: "U \<subseteq> V"
begin

(** Now these names are no longer available for future use, so this is not a great way either *)
private abbreviation pU where "pU \<equiv> MAX v \<in> U. prio v"
private abbreviation \<alpha> where "\<alpha> \<equiv> player_wins_prio pU"
private abbreviation U\<^sub>\<alpha> where "U\<^sub>\<alpha> \<equiv> U \<inter> V_player \<alpha>"
private abbreviation U\<^sub>\<beta> where "U\<^sub>\<beta> \<equiv> U \<inter> V_opponent \<alpha>"
private abbreviation E' :: "'v strat \<Rightarrow> 'v dgraph" where
  "E' \<sigma> \<equiv> E \<inter> ((U\<^sub>\<beta> \<times> U) \<union> E_of_strat \<sigma>)"

definition p_tangle' :: "nat \<Rightarrow> bool" where
  "p_tangle' p \<equiv> p = pU \<and> (\<exists>\<sigma>.
   strategy_of U\<^sub>\<alpha> \<sigma> \<and> ran \<sigma> \<subseteq> U \<and> strongly_connected (E' \<sigma>) \<and>
   (\<forall>v \<in> U\<^sub>\<alpha>. \<forall>ys. cycle_from_node (E' \<sigma>) v ys \<longrightarrow> player_winningP \<alpha> (top_priority ys)))"

lemma "p_tangle' p \<longleftrightarrow> p_tangle p U"
  unfolding p_tangle_def p_tangle'_def
  using ss ne by blast
end

end

end
