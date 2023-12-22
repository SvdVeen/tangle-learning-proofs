theory TangleLearning
imports Main Tangles TangleAttractors
begin

context player_paritygame begin
(** Van Dijk's lemmata. Naming, descriptions will be improved later *)

(** All regions found in the search algorithm are \<alpha>-maximal. This should actually be trivial,
		because they are tangle-attracted regions, so they should be \<alpha>-maximal by definition.
		That is to say: this lemma is not too useful anymore now.
lemma van_dijk_1_player: *)

lemma
	assumes tangles_T: "\<forall>t\<in>T. player_tangle t"
	assumes fin_T: "finite T"
	assumes winning_top_p: "winningP (pr_set V)"
	assumes A_def: "A = {v. v\<in>V \<and> pr v = pr_set V}"
	assumes attr: "player_tangle_attractor T A Z \<sigma>"
	shows "player_\<alpha>_max T Z"
	sorry

(** Lemma 2:
		all plays bound by the tangle attractor strategy \<sigma> that stay in that tangle attractor
		to a region consisting only of vertices of the highest priority, won by \<alpha>, are won by \<alpha>.

		In the search-algorithm, we talk about a region R in the graph that A is inside of, with A
		containing all top priority nodes in R. However, it is easier to prove this assuming we take
		the highest priorities in V. For a final proof then, we have to show that any R is a valid
		subgame.

		Note that we also assume that all tangles in T belong to the player. The final proof will have
		to filter its T based on which player owns the tangles to use this lemma. *)
lemma van_dijk_2_player:
	assumes tangles_T: "\<forall>t\<in>T. player_tangle t"
	assumes fin_T: "finite T"
	assumes winning_top_p: "winningP (pr_set V)"
	assumes A_def: "A = {v. v\<in>V \<and> pr v = pr_set V}"
	assumes attr: "player_tangle_attractor T A Z \<sigma>"
	shows "\<forall>v\<in>Z. \<forall>xs ys.
					lasso (induced_subgraph \<sigma> \<inter> (Z \<times> Z)) v xs ys \<longrightarrow> winning_player ys"
proof (intro ballI allI impI)
	let ?restr_subgraph = "induced_subgraph \<sigma> \<inter> (Z \<times> Z)"
	fix v xs ys
	assume v_in_Z: "v\<in>Z" and lasso_restr_v_xs_ys: "lasso ?restr_subgraph v xs ys"
	from player_tangle_attractor_ss[OF tangles_T fin_T attr] A_def
	have Z_in_V: "Z \<subseteq> V" by blast

	from restr_V_lasso[OF lasso_restr_v_xs_ys] have
		ys_in_Z: "set ys \<subseteq> Z" and
		lasso_v_xs_ys: "lasso (induced_subgraph \<sigma>) v xs ys"
		by blast+
	with Z_in_V have ys_in_V: "set ys \<subseteq> V" by simp

	from lasso_loop[OF lasso_v_xs_ys] obtain y where
		lasso_y_ys: "lasso (induced_subgraph \<sigma>) y [] ys" and
		y_in_ys: "y \<in> set ys" and
		ys_notempty: "ys \<noteq> []"
		by fastforce
	with ys_in_Z have y_in_Z: "y \<in> Z" by blast

	consider (A_in_ys) "set ys \<inter> A \<noteq> {}" | (A_notin_ys) "set ys \<inter> A = {}" by blast
	thus "winning_player ys" proof cases
		case A_in_ys

		have "pr_list ys = pr_set V" proof (rule antisym)
			from pr_list_le_pr_set_V[OF ys_in_V ys_notempty]
			show "pr_list ys \<le> pr_set V" .
		next
			from A_in_ys A_def show "pr_set V \<le> pr_list ys"
				unfolding pr_list_def
				using Max_ge[OF finite_surj[OF fin_V image_mono[OF ys_in_V, of pr]]]
				by fastforce
		qed

		with winning_top_p show ?thesis by simp
	next
		case A_notin_ys
		with player_tangle_attractor_strat[OF tangles_T fin_T attr] y_in_Z lasso_y_ys
		show ?thesis by fastforce
	qed
qed

lemma "x \<notin> dom \<sigma> \<Longrightarrow> induced_subgraph \<sigma> \<subseteq> induced_subgraph (\<sigma>(x\<mapsto>y))"
	unfolding induced_subgraph_def E_of_strat_def by force

xxx, sorry

(** From anywhere in the tangle-attracted region Z to A, the opponent can reach a node of priority
		p (the top priority in the current region) *)
lemma van_dijk_3_player:
	assumes tangles_T: "\<forall>t\<in>T. player_tangle t"
	assumes fin_T: "finite T"
	assumes A_def: "A = {v. v\<in>V \<and> pr v = pr_set V}"
	assumes attr: "player_tangle_attractor T A Z \<sigma>"
	shows "\<forall>v\<in>Z. \<exists>v'. pr v' = pr_set V \<and> (\<exists>vs. path (induced_subgraph \<sigma>) v	vs v')"
	using tangles_T fin_T attr
proof (induction rule: player_tangle_attractor_induct)
	case base thus ?case
		apply (rule ballI)
		subgoal for v
			apply (rule exI[where x="v"]; rule conjI)
			subgoal using A_def by simp
			subgoal apply (rule exI[where x="[]"]) by simp
			done
		done
next
	case (own x S y \<sigma>)
	show ?case proof (rule ballI)
		fix v assume v_in_S': "v \<in> insert x S"
		consider (x) "v=x" | (not_x) "v\<noteq>x" by blast
		thus "\<exists>v'. pr v' = pr_set V \<and> (\<exists>vs. path (induced_subgraph (\<sigma>(x\<mapsto>y))) v vs v')"
		proof cases
			case x
			then show ?thesis sorry
		next
			case not_x
			then show ?thesis sorry
		qed
	qed
next
	case (opponent x S \<sigma>)
	show ?case proof (rule ballI)
		fix v assume v_in_S': "v \<in> insert x S"
		consider (x) "v=x" | (not_x) "v\<noteq>x" by blast
		thus "\<exists>v'. pr v' = pr_set V \<and> (\<exists>vs. path (induced_subgraph \<sigma>) v vs v')"
		proof cases
			case x with opponent obtain y where
			edge_in_E: "(x,y) \<in> E" and
			edge_in_subgraph: "(x,y) \<in> induced_subgraph \<sigma>"
			using succ ind_subgraph_notin_dom
			by blast

		with opponent.IH opponent.hyps(2) obtain x' ys where
			pr_x': "pr x' = pr_set V" and
			path_y_ys_x': "path (induced_subgraph \<sigma>) y ys x'"
			by blast
		from path_y_ys_x' edge_in_subgraph x have path_v_x':
			"path (induced_subgraph \<sigma>) v (x#ys) x'" by auto
		show ?thesis
			apply (rule exI[where x="x'"]; rule conjI)
			subgoal using pr_x' .
			subgoal apply (rule exI[where x="x#ys"]) using path_v_x' by blast
			done
		next
			case not_x with v_in_S' opponent show ?thesis by blast
		qed
	qed
next
	case (escape t S \<sigma>' \<sigma>)
	show ?case sorry
qed

(** For each new tangle t, all successors of t are in higher \<alpha>-regions.
		The regions no longer have an assigned \<alpha> in the updated algorithm, so this needs some rephrasing.
lemma van_dijk_4_player: *)

(** Every nontrivial bottom SCC B of the reduced region restricted by witness strategy \<sigma> is a unique
		tangle
lemma van_dijk_5_player: *)

(** The lowest region in the decomposition always contains a tangle.
lemma van_dijk_6_player: *)

(** A tangle t is a dominion (what we call a winning region) if and only if it has no escapes *)
lemma van_dijk_7_player:
	assumes t_tangle: "player_tangle t"
	shows "opponent_escapes t = {} \<longleftrightarrow> player_winning_region t"
	using assms no_escapes_closed_opponent closed_player_tangle_is_winning_region
	by safe (auto simp: player_winning_region_def)

(** Every tangle t found in the highest region of player \<alpha> has no escapes.
lemma van_dijk_8_player: *)

(** The search algorithm terminates by finding a dominion.
lemma van_dijk_9_player: *)

(** The solve algorithm solves parity games.
		Tom suggested approaching this the same way we "proved" Zielonka's algorithm when we proved
		positional determinancy earlier; which would mean we prove positional determinancy again, but
		with a proof that follows the steps of tangle learning.
lemma van_dijk_10_player: *)

xxx, sorry
(** Every bottom SCC in a dominion (what we call a winning region) is a closed tangle. *)
lemma
	assumes dominion_R: "player_winning_region R"
	assumes U_in_R: "U \<subseteq> R"
	assumes bottom_SCC_U: "bottom_SCC U"
	shows "player_tangle U \<and> E `` U \<subseteq> U"
proof (rule conjI)
	from bottom_SCC_closed[OF bottom_SCC_U]
	show U_closed: "E `` U \<subseteq> U" . (** This one is trivial *)

	from bottom_SCC_U have U_notempty: "U \<noteq> {}" by auto
	from bottom_SCC_finite[OF bottom_SCC_U] have fin_U[simp]: "finite U" .
	from bottom_SCC_in_V[OF bottom_SCC_U] have U_in_V: "U\<subseteq>V" .

	from dominion_R obtain \<sigma> where
		\<sigma>_strat: "strategy_of V\<^sub>\<alpha> \<sigma>" and
		\<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> R" and
		\<sigma>_ran: "ran \<sigma> \<subseteq> R" and
		\<sigma>_winning: "\<forall>v\<in>R. \<forall>xs. reachable_cycle (induced_subgraph \<sigma>) v xs
								\<longrightarrow> winning_player xs" and
		R_closed_opponent: "E `` (R\<inter>V\<^sub>\<beta>) \<subseteq> R"
		unfolding player_winning_region_def by fastforce

	have "(induced_subgraph (dom \<sigma>) \<sigma>) \<inter> U\<times>U \<subseteq> E \<inter> U\<times>U"
		by auto

	have pr_list_winning: "winningP (pr_set U)"
	proof -
		(** I will need to show that all the highest priority in U is won by the player.
				My intuition says this should hold because every cycle is won by the player since it is
				part of the winning region. Since this is an SCC, the node of the highest priority in U
				is part of a cycle, and that cycle should be won by \<alpha>. *)
		obtain y where
			y_in_U: "y\<in>U" and
			y_pr_list: "pr y = pr_set U"
			using pr_set_exists[OF fin_U U_notempty] ..

		then obtain ys where cycle_y_ys: "cycle (E\<inter>U\<times>U) y ys"
			using bottom_SCC_cycle[OF bottom_SCC_U] by blast
		hence path_y_ys_y: "path (E\<inter>U\<times>U) y ys y" and ys_notempty: "ys \<noteq> []"
			by (simp add: cycle_iff_loop[of "(E\<inter>U\<times>U)" y ys])+

		from dominion_R have "True"
			unfolding player_winning_region_def sorry

		show ?thesis sorry
	qed

	show "player_tangle U"
		unfolding player_tangle_def
		apply (intro conjI)
		subgoal using U_notempty .
		subgoal using U_in_V .
		subgoal using pr_list_winning .
		subgoal unfolding player_tangle_strat_def Let_def sorry
		done
qed

end (** End of context player_paritygame *)

context paritygame begin

(** The future proof still needs to show that this is limited to a region R, which is a subgame. *)
lemma van_dijk_2:
	assumes fin_T: "finite T"
	assumes winning_top_p: "player_winningP \<alpha> (pr_set V)"
	assumes A_def: "A = {v. v\<in>V \<and> pr v = pr_set V}"
	assumes attr: "tangle_attractor \<alpha> T A Z \<sigma>"
	shows "\<forall>v\<in>Z. \<forall>xs ys. lasso (Restr (induced_subgraph \<sigma>) Z) v xs ys
						\<longrightarrow> player_wins_list \<alpha> ys"
	using assms
	using P0.van_dijk_2_player[of "{t\<in>T. tangle EVEN t}"]
	using P1.van_dijk_2_player[of "{t\<in>T. tangle ODD t}"]
	by (cases \<alpha>) auto

lemma van_dijk_7:
	assumes "tangle \<alpha> t"
	shows "escapes \<alpha> t = {} \<longleftrightarrow> winning_region \<alpha> t"
	using assms P0.van_dijk_7_player P1.van_dijk_7_player
	by (cases \<alpha>; simp)

end (** End of context paritygame *)

end
