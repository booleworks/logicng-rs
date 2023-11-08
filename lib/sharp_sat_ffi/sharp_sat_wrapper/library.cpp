#include <deque>
#include <memory>
#include "include/library.h"

namespace wrapper {

    Solver *new_solver() {
        return new InteractiveSolver{};
    }

    void drop_solver(Solver* solver) {
        delete solver;
    }

    void add_clause(Solver* solver, int32_t const* clauses, uint32_t size) {
        solver->add_clause(clauses, size);
    }

    const std::string& solve(Solver* solver) {
        std::cout.setstate(std::ios_base::failbit);
        solver->solve();
        std::cout.clear();
        return solver->last_result;
    }
}

InteractiveSolver::InteractiveSolver() {
    stopwatch_.setTimeBound(config_.time_bound_seconds);

    literal_pool_.clear();
    literal_pool_.push_back(SENTINEL_LIT);

    variables_.clear();
    variables_.push_back(Variable()); //initializing the Sentinel

    literal_values_.clear();
    unit_clauses_.clear();
    occurrence_lists_.clear();
    literals_.clear();
}
//variables resize, literal_values resize, conflict_clauses reserve, literal_pool reserve, occurence_lists_ resize, literals_resize
void InteractiveSolver::add_clause(int32_t const *clause, uint32_t size) {
    std::vector<LiteralID> literals;

    bool skip_clause{false};
    for (auto i{0}; i < size; ++i) {
        bool duplicate_literal{false};
        int32_t lit{clause[i]};
        for (auto old_lit: literals) {
            if (old_lit.toInt() == lit) {
                duplicate_literal = true;
                break;
            }
            if (old_lit.toInt() == -lit) {
                skip_clause = true;
                break;
            }
        }
        if (!duplicate_literal) {
            literals.push_back(lit);
            nVars = std::max(nVars, static_cast<unsigned>(std::abs(lit)));
        }
    }
    literals_.resize(nVars + 1);
    occurrence_lists_.resize(nVars + 1);
    if (!skip_clause) {
        assert(!literals.empty());
        ++clauses_added;
        statistics_.incorporateClauseData(literals);
        ClauseOfs cl_ofs = addClause(literals);
        if (literals.size() >= 3) {
            for (auto l: literals) {
                occurrence_lists_[l].push_back(cl_ofs);
            }
        }
    }
}

void InteractiveSolver::solve() {
    variables_.resize(nVars + 1);
    literal_values_.resize(nVars + 1, X_TRI);
    // occurrence_lists_.resize(nVars + 1);
    // literals_.resize(nVars + 1);

    conflict_clauses_.reserve(2*clauses_added);

    stopwatch_.start();
    initStack(num_variables());

    bool notFoundUNSAT = simplePreProcess();
    if (notFoundUNSAT) {
        last_ccl_deletion_time_ = last_ccl_cleanup_time_ = statistics_.getTime();
        violated_clause.reserve(num_variables());
        comp_manager_.initialize(literals_, literal_pool_);
        statistics_.exit_state_ = countSAT();
        statistics_.set_final_solution_count(stack_.top().getTotalModelCount());
        statistics_.num_long_conflict_clauses_ = num_conflict_clauses();
    } else {
        statistics_.exit_state_ = SUCCESS;
        statistics_.set_final_solution_count(0.0);
    }

    stopwatch_.stop();
    statistics_.time_elapsed_ = stopwatch_.getElapsedSeconds();
    last_result = statistics_.final_solution_count_.get_str(10);
}

bool InteractiveSolver::simplePreProcess() {
    if (!config_.perform_pre_processing) {
        return true;
    }
    assert(literal_stack_.size() == 0);
    unsigned start_ofs = 0;
    for (auto lit: unit_clauses_) {
        setLiteralIfFree(lit);
    }
    bool succeeded = BCP(start_ofs);
    if (succeeded) {
        succeeded &= prepFailedLiteralTest();
    }
    if (succeeded) {
        HardWireAndCompact();
    }
    return succeeded;
}

bool InteractiveSolver::prepFailedLiteralTest() {
    unsigned last_size;
    do {
        last_size = literal_stack_.size();
        for (unsigned v = 1; v < variables_.size(); v++)
            if (isActive(v)) {
                unsigned sz = literal_stack_.size();
                setLiteralIfFree(LiteralID(v, true));
                bool res = BCP(sz);
                while (literal_stack_.size() > sz) {
                    unSet(literal_stack_.back());
                    literal_stack_.pop_back();
                }

                if (!res) {
                    sz = literal_stack_.size();
                    setLiteralIfFree(LiteralID(v, false));
                    if (!BCP(sz))
                        return false;
                } else {

                    sz = literal_stack_.size();
                    setLiteralIfFree(LiteralID(v, false));
                    bool resb = BCP(sz);
                    while (literal_stack_.size() > sz) {
                        unSet(literal_stack_.back());
                        literal_stack_.pop_back();
                    }
                    if (!resb) {
                        sz = literal_stack_.size();
                        setLiteralIfFree(LiteralID(v, true));
                        if (!BCP(sz))
                            return false;
                    }
                }
            }
    } while (literal_stack_.size() > last_size);

    return true;
}

void InteractiveSolver::HardWireAndCompact() {
    compactClauses();
    compactVariables();
    literal_stack_.clear();

    for (auto l = LiteralID(1, false); l != literals_.end_lit(); l.inc()) {
        literal(l).activity_score_ = literal(l).binary_links_.size() - 1;
        literal(l).activity_score_ += occurrence_lists_[l].size();
    }

    statistics_.num_unit_clauses_ = unit_clauses_.size();

    statistics_.num_original_binary_clauses_ = statistics_.num_binary_clauses_;
    statistics_.num_original_unit_clauses_ = statistics_.num_unit_clauses_ =
            unit_clauses_.size();
    initStack(num_variables());
    original_lit_pool_size_ = literal_pool_.size();
}

SOLVER_StateT InteractiveSolver::countSAT() {
    retStateT state = RESOLVED;

    while (true) {
        while (comp_manager_.findNextRemainingComponentOf(stack_.top())) {
            decideLiteral();
            if (stopwatch_.timeBoundBroken())
                return TIMEOUT;

            while (!bcp()) {
                state = resolveConflict();
                if (state == BACKTRACK)
                    break;
            }
            if (state == BACKTRACK)
                break;
        }

        state = backtrack();
        if (state == EXIT)
            return SUCCESS;
        while (state != PROCESS_COMPONENT && !bcp()) {
            state = resolveConflict();
            if (state == BACKTRACK) {
                state = backtrack();
                if (state == EXIT)
                    return SUCCESS;
            }
        }
    }
    return SUCCESS;
}

void InteractiveSolver::decideLiteral() {
    // establish another decision stack level
    stack_.push_back(StackLevel(stack_.top().currentRemainingComponent(), literal_stack_.size(),
                                comp_manager_.component_stack_size()));
    float max_score = -1;
    float score;
    unsigned max_score_var = 0;
    for (auto it = comp_manager_.superComponentOf(stack_.top()).varsBegin(); *it != varsSENTINEL; it++) {
        score = scoreOf(*it);
        if (score > max_score) {
            max_score = score;
            max_score_var = *it;
        }
    }
    // this assert should always hold,
    // if not then there is a bug in the logic of countSAT();
    assert(max_score_var != 0);

    LiteralID theLit(max_score_var, literal(LiteralID(max_score_var, true)).activity_score_ >
                                    literal(LiteralID(max_score_var, false)).activity_score_);

    setLiteralIfFree(theLit);
    statistics_.num_decisions_++;

    if (statistics_.num_decisions_ % 128 == 0)
//    if (statistics_.num_conflicts_ % 128 == 0)
        decayActivities();
    // decayActivitiesOf(comp_manager_.superComponentOf(stack_.top()));
    assert(stack_.top().remaining_components_ofs() <= comp_manager_.component_stack_size());
}

retStateT InteractiveSolver::backtrack() {
    assert(
            stack_.top().remaining_components_ofs() <= comp_manager_.component_stack_size());
    do {
        if (stack_.top().branch_found_unsat())
            comp_manager_.removeAllCachePollutionsOf(stack_.top());
        else if (stack_.top().anotherCompProcessible())
            return PROCESS_COMPONENT;

        if (!stack_.top().isSecondBranch()) {
            LiteralID aLit = TOS_decLit();
            assert(stack_.get_decision_level() > 0);
            stack_.top().changeBranch();
            reactivateTOS();
            setLiteralIfFree(aLit.neg(), NOT_A_CLAUSE);
            return RESOLVED;
        }
        // OTHERWISE:  backtrack further
        comp_manager_.cacheModelCountOf(stack_.top().super_component(),
                                        stack_.top().getTotalModelCount());

        if (stack_.get_decision_level() <= 0)
            break;
        reactivateTOS();

        assert(stack_.size()>=2);
        (stack_.end() - 2)->includeSolution(stack_.top().getTotalModelCount());
        stack_.pop_back();
        // step to the next component not yet processed
        stack_.top().nextUnprocessedComponent();

        assert(
                stack_.top().remaining_components_ofs() < comp_manager_.component_stack_size()+1);

    } while (stack_.get_decision_level() >= 0);
    return EXIT;
}

bool InteractiveSolver::bcp() {
// the asserted literal has been set, so we start
// bcp on that literal
    unsigned start_ofs = literal_stack_.size() - 1;

//BEGIN process unit clauses
    for (auto lit : unit_clauses_)
        setLiteralIfFree(lit);
//END process unit clauses

    bool bSucceeded = BCP(start_ofs);

    if (config_.perform_failed_lit_test && bSucceeded) {
        bSucceeded = implicitBCP();
    }
    return bSucceeded;
}

bool InteractiveSolver::implicitBCP() {
    static vector<LiteralID> test_lits(num_variables());
    static LiteralIndexedVector<unsigned char> viewed_lits(num_variables() + 1, 0);

    unsigned stack_ofs = stack_.top().literal_stack_ofs();
    unsigned num_curr_lits = 0;
    while (stack_ofs < literal_stack_.size()) {
        test_lits.clear();
        for (auto it = literal_stack_.begin() + stack_ofs;
             it != literal_stack_.end(); it++) {
            for (auto cl_ofs : occurrence_lists_[it->neg()])
                if (!isSatisfied(cl_ofs)) {
                    for (auto lt = beginOf(cl_ofs); *lt != SENTINEL_LIT; lt++)
                        if (isActive(*lt) && !viewed_lits[lt->neg()]) {
                            test_lits.push_back(lt->neg());
                            viewed_lits[lt->neg()] = true;

                        }
                }
        }
        num_curr_lits = literal_stack_.size() - stack_ofs;
        stack_ofs = literal_stack_.size();
        for (auto jt = test_lits.begin(); jt != test_lits.end(); jt++)
            viewed_lits[*jt] = false;

        vector<float> scores;
        scores.clear();
        for (auto jt = test_lits.begin(); jt != test_lits.end(); jt++) {
            scores.push_back(literal(*jt).activity_score_);
        }
        sort(scores.begin(), scores.end());
        num_curr_lits = 10 + num_curr_lits / 20;
        float threshold = 0.0;
        if (scores.size() > num_curr_lits) {
            threshold = scores[scores.size() - num_curr_lits];
        }

        statistics_.num_failed_literal_tests_ += test_lits.size();

        for (auto lit : test_lits)
            if (isActive(lit) && threshold <= literal(lit).activity_score_) {
                unsigned sz = literal_stack_.size();
                // we increase the decLev artificially
                // s.t. after the tentative BCP call, we can learn a conflict clause
                // relative to the assignment of *jt
                stack_.startFailedLitTest();
                setLiteralIfFree(lit);

                assert(!hasAntecedent(lit));

                bool bSucceeded = BCP(sz);
                if (!bSucceeded)
                    recordAllUIPCauses();

                stack_.stopFailedLitTest();

                while (literal_stack_.size() > sz) {
                    unSet(literal_stack_.back());
                    literal_stack_.pop_back();
                }

                if (!bSucceeded) {
                    statistics_.num_failed_literals_detected_++;
                    sz = literal_stack_.size();
                    for (auto it = uip_clauses_.rbegin();
                         it != uip_clauses_.rend(); it++) {
                        // DEBUG
                        if (it->size() == 0)
                            cout << "EMPTY CLAUSE FOUND" << endl;
                        // END DEBUG
                        setLiteralIfFree(it->front(),
                                         addUIPConflictClause(*it));
                    }
                    if (!BCP(sz))
                        return false;
                }
            }
    }
    return true;
}

bool InteractiveSolver::BCP(unsigned start_at_stack_ofs) {
    for (unsigned int i = start_at_stack_ofs; i < literal_stack_.size(); i++) {
        LiteralID unLit = literal_stack_[i].neg();
        //BEGIN Propagate Bin Clauses
        for (auto bt = literal(unLit).binary_links_.begin();
             *bt != SENTINEL_LIT; bt++) {
            if (isResolved(*bt)) {
                setConflictState(unLit, *bt);
                return false;
            }
            setLiteralIfFree(*bt, Antecedent(unLit));
        }
        //END Propagate Bin Clauses
        for (auto itcl = literal(unLit).watch_list_.rbegin();
             *itcl != SENTINEL_CL; itcl++) {
            bool isLitA = (*beginOf(*itcl) == unLit);
            auto p_watchLit = beginOf(*itcl) + 1 - isLitA;
            auto p_otherLit = beginOf(*itcl) + isLitA;

            if (isSatisfied(*p_otherLit))
                continue;
            auto itL = beginOf(*itcl) + 2;
            while (isResolved(*itL))
                itL++;
            // either we found a free or satisfied lit
            if (*itL != SENTINEL_LIT) {
                literal(*itL).addWatchLinkTo(*itcl);
                swap(*itL, *p_watchLit);
                *itcl = literal(unLit).watch_list_.back();
                literal(unLit).watch_list_.pop_back();
            } else {
                // or p_unLit stays resolved
                // and we have hence no free literal left
                // for p_otherLit remain poss: Active or Resolved
                if (setLiteralIfFree(*p_otherLit, Antecedent(*itcl))) { // implication
                    if (isLitA)
                        swap(*p_otherLit, *p_watchLit);
                } else {
                    setConflictState(*itcl);
                    return false;
                }
            }
        }
    }
    return true;
}

retStateT InteractiveSolver::resolveConflict() {
    recordLastUIPCauses();

    if (statistics_.num_clauses_learned_ - last_ccl_deletion_time_
        > statistics_.clause_deletion_interval()) {
        deleteConflictClauses();
        last_ccl_deletion_time_ = statistics_.num_clauses_learned_;
    }

    if (statistics_.num_clauses_learned_ - last_ccl_cleanup_time_ > 100000) {
        compactConflictLiteralPool();
        last_ccl_cleanup_time_ = statistics_.num_clauses_learned_;
    }

    statistics_.num_conflicts_++;

    assert(
            stack_.top().remaining_components_ofs() <= comp_manager_.component_stack_size());

    assert(uip_clauses_.size() == 1);

    // DEBUG
    if (uip_clauses_.back().size() == 0)
        cout << " EMPTY CLAUSE FOUND" << endl;
    // END DEBUG

    stack_.top().mark_branch_unsat();
    //BEGIN Backtracking
    // maybe the other branch had some solutions
    if (stack_.top().isSecondBranch()) {
        return BACKTRACK;
    }

    Antecedent ant(NOT_A_CLAUSE);
    // this has to be checked since using implicit BCP
    // and checking literals there not exhaustively
    // we cannot guarantee that uip_clauses_.back().front() == TOS_decLit().neg()
    // this is because we might have checked a literal
    // during implict BCP which has been a failed literal
    // due only to assignments made at lower decision levels
    if (uip_clauses_.back().front() == TOS_decLit().neg()) {
        assert(TOS_decLit().neg() == uip_clauses_.back()[0]);
        var(TOS_decLit().neg()).ante = addUIPConflictClause(
                uip_clauses_.back());
        ant = var(TOS_decLit()).ante;
    }
    assert(stack_.get_decision_level() > 0);
    assert(stack_.top().branch_found_unsat());

    // we do not have to remove pollutions here,
    // since conflicts only arise directly before
    // remaining components are stored
    // hence
    assert(
            stack_.top().remaining_components_ofs() == comp_manager_.component_stack_size());

    stack_.top().changeBranch();
    LiteralID lit = TOS_decLit();
    reactivateTOS();
    setLiteralIfFree(lit.neg(), ant);
//END Backtracking
    return RESOLVED;
}

void InteractiveSolver::recordLastUIPCauses() {
// note:
// variables of lower dl: if seen we dont work with them anymore
// variables of this dl: if seen we incorporate their
// antecedent and set to unseen
    bool seen[num_variables() + 1];
    memset(seen, false, sizeof(bool) * (num_variables() + 1));

    static vector<LiteralID> tmp_clause;
    tmp_clause.clear();

    assertion_level_ = 0;
    uip_clauses_.clear();

    unsigned lit_stack_ofs = literal_stack_.size();
    int DL = stack_.get_decision_level();
    unsigned lits_at_current_dl = 0;

    for (auto l : violated_clause) {
        if (var(l).decision_level == 0 || existsUnitClauseOf(l.var()))
            continue;
        if (var(l).decision_level < DL)
            tmp_clause.push_back(l);
        else
            lits_at_current_dl++;
        literal(l).increaseActivity();
        seen[l.var()] = true;
    }

    LiteralID curr_lit;
    while (lits_at_current_dl) {
        assert(lit_stack_ofs != 0);
        curr_lit = literal_stack_[--lit_stack_ofs];

        if (!seen[curr_lit.var()])
            continue;

        seen[curr_lit.var()] = false;

        if (lits_at_current_dl-- == 1) {
            // perform UIP stuff
            if (!hasAntecedent(curr_lit)) {
                // this should be the decision literal when in first branch
                // or it is a literal decided to explore in failed literal testing
                //assert(stack_.TOS_decLit() == curr_lit);
//				cout << "R" << curr_lit.toInt() << "S"
//				     << var(curr_lit).ante.isAnt() << " "  << endl;
                break;
            }
        }

        assert(hasAntecedent(curr_lit));

        //cout << "{" << curr_lit.toInt() << "}";
        if (getAntecedent(curr_lit).isAClause()) {
            updateActivities(getAntecedent(curr_lit).asCl());
            assert(curr_lit == *beginOf(getAntecedent(curr_lit).asCl()));

            for (auto it = beginOf(getAntecedent(curr_lit).asCl()) + 1;
                 *it != SENTINEL_CL; it++) {
                if (seen[it->var()] || (var(*it).decision_level == 0)
                    || existsUnitClauseOf(it->var()))
                    continue;
                if (var(*it).decision_level < DL)
                    tmp_clause.push_back(*it);
                else
                    lits_at_current_dl++;
                seen[it->var()] = true;
            }
        } else {
            LiteralID alit = getAntecedent(curr_lit).asLit();
            literal(alit).increaseActivity();
            literal(curr_lit).increaseActivity();
            if (!seen[alit.var()] && !(var(alit).decision_level == 0)
                && !existsUnitClauseOf(alit.var())) {
                if (var(alit).decision_level < DL)
                    tmp_clause.push_back(alit);
                else
                    lits_at_current_dl++;
                seen[alit.var()] = true;
            }
        }
        curr_lit = NOT_A_LIT;
    }

//	cout << "T" << curr_lit.toInt() << "U "
//     << var(curr_lit).decision_level << ", " << stack_.get_decision_level() << endl;
//	cout << "V"  << var(curr_lit).ante.isAnt() << " "  << endl;
    minimizeAndStoreUIPClause(curr_lit.neg(), tmp_clause, seen);

//	if (var(curr_lit).decision_level > assertion_level_)
//		assertion_level_ = var(curr_lit).decision_level;
}

void InteractiveSolver::recordAllUIPCauses() {
// note:
// variables of lower dl: if seen we dont work with them anymore
// variables of this dl: if seen we incorporate their
// antecedent and set to unseen
    bool seen[num_variables() + 1];
    memset(seen, false, sizeof(bool) * (num_variables() + 1));

    static vector<LiteralID> tmp_clause;
    tmp_clause.clear();

    assertion_level_ = 0;
    uip_clauses_.clear();

    unsigned lit_stack_ofs = literal_stack_.size();
    int DL = stack_.get_decision_level();
    unsigned lits_at_current_dl = 0;

    for (auto l : violated_clause) {
        if (var(l).decision_level == 0 || existsUnitClauseOf(l.var()))
            continue;
        if (var(l).decision_level < DL)
            tmp_clause.push_back(l);
        else
            lits_at_current_dl++;
        literal(l).increaseActivity();
        seen[l.var()] = true;
    }
    unsigned n = 0;
    LiteralID curr_lit;
    while (lits_at_current_dl) {
        assert(lit_stack_ofs != 0);
        curr_lit = literal_stack_[--lit_stack_ofs];

        if (!seen[curr_lit.var()])
            continue;

        seen[curr_lit.var()] = false;

        if (lits_at_current_dl-- == 1) {
            n++;
            if (!hasAntecedent(curr_lit)) {
                // this should be the decision literal when in first branch
                // or it is a literal decided to explore in failed literal testing
                //assert(stack_.TOS_decLit() == curr_lit);
                break;
            }
            // perform UIP stuff
            minimizeAndStoreUIPClause(curr_lit.neg(), tmp_clause, seen);
        }

        assert(hasAntecedent(curr_lit));

        if (getAntecedent(curr_lit).isAClause()) {
            updateActivities(getAntecedent(curr_lit).asCl());
            assert(curr_lit == *beginOf(getAntecedent(curr_lit).asCl()));

            for (auto it = beginOf(getAntecedent(curr_lit).asCl()) + 1;
                 *it != SENTINEL_CL; it++) {
                if (seen[it->var()] || (var(*it).decision_level == 0)
                    || existsUnitClauseOf(it->var()))
                    continue;
                if (var(*it).decision_level < DL)
                    tmp_clause.push_back(*it);
                else
                    lits_at_current_dl++;
                seen[it->var()] = true;
            }
        } else {
            LiteralID alit = getAntecedent(curr_lit).asLit();
            literal(alit).increaseActivity();
            literal(curr_lit).increaseActivity();
            if (!seen[alit.var()] && !(var(alit).decision_level == 0)
                && !existsUnitClauseOf(alit.var())) {
                if (var(alit).decision_level < DL)
                    tmp_clause.push_back(alit);
                else
                    lits_at_current_dl++;
                seen[alit.var()] = true;
            }
        }
    }
    if (!hasAntecedent(curr_lit)) {
        minimizeAndStoreUIPClause(curr_lit.neg(), tmp_clause, seen);
    }
}

void InteractiveSolver::minimizeAndStoreUIPClause(LiteralID uipLit, vector<LiteralID> &tmp_clause, bool seen[]) {
    static deque<LiteralID> clause;
    clause.clear();
    assertion_level_ = 0;
    for (auto lit : tmp_clause) {
        if (existsUnitClauseOf(lit.var()))
            continue;
        bool resolve_out = false;
        if (hasAntecedent(lit)) {
            resolve_out = true;
            if (getAntecedent(lit).isAClause()) {
                for (auto it = beginOf(getAntecedent(lit).asCl()) + 1;
                     *it != SENTINEL_CL; it++)
                    if (!seen[it->var()]) {
                        resolve_out = false;
                        break;
                    }
            } else if (!seen[getAntecedent(lit).asLit().var()]) {
                resolve_out = false;
            }
        }

        if (!resolve_out) {
            // uipLit should be the sole literal of this Decision Level
            if (var(lit).decision_level >= assertion_level_) {
                assertion_level_ = var(lit).decision_level;
                clause.push_front(lit);
            } else
                clause.push_back(lit);
        }
    }

    if(uipLit.var())
        assert(var(uipLit).decision_level == stack_.get_decision_level());

    //assert(uipLit.var() != 0);
    if (uipLit.var() != 0)
        clause.push_front(uipLit);
    uip_clauses_.push_back(vector<LiteralID>(clause.begin(), clause.end()));
}