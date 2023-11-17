/*
 * component_archetype.h
 *
 *  Created on: Feb 9, 2013
 *      Author: mthurley
 */

#ifndef COMPONENT_ARCHETYPE_H_
#define COMPONENT_ARCHETYPE_H_


#include "../primitive_types.h"
#include "component.h"


#include "cacheable_component.h"





#include <cstring>
#include <algorithm>



#include <iostream>
// State values for variables found during component
// analysis (CA)
typedef unsigned char CA_SearchState;
#define   CA_NIL  0
#define   CA_VAR_IN_SUP_COMP_UNSEEN  1
#define   CA_VAR_SEEN 2
#define   CA_VAR_IN_OTHER_COMP  4

#define   CA_VAR_MASK  7

#define   CA_CL_IN_SUP_COMP_UNSEEN  8
#define   CA_CL_SEEN 16
#define   CA_CL_IN_OTHER_COMP  32
#define   CA_CL_ALL_LITS_ACTIVE  64

#define   CA_CL_MASK  120

class StackLevel;

class ComponentArchetype {
public:
  ComponentArchetype(ComponentArchetypeState* state) {
      static_state = state;
  }
  ComponentArchetype(StackLevel &stack_level, Component &super_comp, ComponentArchetypeState* state) :
      p_super_comp_(&super_comp), p_stack_level_(&stack_level) {
      static_state = state;
  }

  void reInitialize(StackLevel &stack_level, Component &super_comp, ComponentArchetypeState* state) {
    static_state = state;
    p_super_comp_ = &super_comp;
    p_stack_level_ = &stack_level;
    clearArrays(static_state);
    current_comp_for_caching_.reserveSpace(super_comp.num_variables(),super_comp.numLongClauses());
  }

  Component &super_comp() {
    return *p_super_comp_;
  }

  StackLevel & stack_level() {
    return *p_stack_level_;
  }

  void setVar_in_sup_comp_unseen(VariableIndex v) {
    static_state->seen_[v] = CA_VAR_IN_SUP_COMP_UNSEEN | (static_state->seen_[v] & CA_CL_MASK);
  }

  void setClause_in_sup_comp_unseen(ClauseIndex cl) {
      static_state->seen_[cl] = CA_CL_IN_SUP_COMP_UNSEEN | (static_state->seen_[cl] & CA_VAR_MASK);
  }

  void setVar_nil(VariableIndex v) {
      static_state->seen_[v] &= CA_CL_MASK;
  }

  void setClause_nil(ClauseIndex cl) {
      static_state->seen_[cl] &= CA_VAR_MASK;
  }

  void setVar_seen(VariableIndex v) {
      static_state->seen_[v] = CA_VAR_SEEN | (static_state->seen_[v] & CA_CL_MASK);
  }

  void setClause_seen(ClauseIndex cl) {
    setClause_nil(cl);
      static_state->seen_[cl] = CA_CL_SEEN | (static_state->seen_[cl] & CA_VAR_MASK);
  }

  void setClause_seen(ClauseIndex cl, bool all_lits_act) {
      setClause_nil(cl);
      static_state->seen_[cl] = CA_CL_SEEN | (all_lits_act?CA_CL_ALL_LITS_ACTIVE:0) | (static_state->seen_[cl] & CA_VAR_MASK);
    }

  void setVar_in_other_comp(VariableIndex v) {
      static_state->seen_[v] = CA_VAR_IN_OTHER_COMP | (static_state->seen_[v] & CA_CL_MASK);
  }

  void setClause_in_other_comp(ClauseIndex cl) {
      static_state->seen_[cl] = CA_CL_IN_OTHER_COMP | (static_state->seen_[cl] & CA_VAR_MASK);
  }

  bool var_seen(VariableIndex v) {
    return static_state->seen_[v] & CA_VAR_SEEN;
  }

  bool clause_seen(ClauseIndex cl) {
    return static_state->seen_[cl] & CA_CL_SEEN;
  }

  bool clause_all_lits_active(ClauseIndex cl) {
    return static_state->seen_[cl] & CA_CL_ALL_LITS_ACTIVE;
  }
  void setClause_all_lits_active(ClauseIndex cl) {
      static_state->seen_[cl] |= CA_CL_ALL_LITS_ACTIVE;
  }

  bool var_nil(VariableIndex v) {
    return (static_state->seen_[v] & CA_VAR_MASK) == 0;
  }

  bool clause_nil(ClauseIndex cl) {
    return (static_state->seen_[cl] & CA_CL_MASK) == 0;
  }

  bool var_unseen_in_sup_comp(VariableIndex v) {
    return static_state->seen_[v] & CA_VAR_IN_SUP_COMP_UNSEEN;
  }

  bool clause_unseen_in_sup_comp(ClauseIndex cl) {
    return static_state->seen_[cl] & CA_CL_IN_SUP_COMP_UNSEEN;
  }

  bool var_seen_in_peer_comp(VariableIndex v) {
    return static_state->seen_[v] & CA_VAR_IN_OTHER_COMP;
  }

  bool clause_seen_in_peer_comp(ClauseIndex cl) {
    return static_state->seen_[cl] & CA_CL_IN_OTHER_COMP;
  }

  static void initArrays(unsigned max_variable_id, unsigned max_clause_id, ComponentArchetypeState* s) {
    unsigned seen_size = std::max(max_variable_id,max_clause_id)  + 1;
    s->seen_ = new CA_SearchState[seen_size];
      s->seen_byte_size_ = sizeof(CA_SearchState) * (seen_size);
    clearArrays(s);

  }

  static void clearArrays(ComponentArchetypeState* s) {
    memset(s->seen_, CA_NIL, s->seen_byte_size_);
  }


  Component *makeComponentFromState(unsigned stack_size) {
    Component *p_new_comp = new Component();
    p_new_comp->reserveSpace(stack_size, super_comp().numLongClauses());
    current_comp_for_caching_.clear();

    for (auto v_it = super_comp().varsBegin(); *v_it != varsSENTINEL;  v_it++)
      if (var_seen(*v_it)) { //we have to put a var into our component
        p_new_comp->addVar(*v_it);
        current_comp_for_caching_.addVar(*v_it);
        setVar_in_other_comp(*v_it);
      }
    p_new_comp->closeVariableData();
    current_comp_for_caching_.closeVariableData();

    for (auto it_cl = super_comp().clsBegin(); *it_cl != clsSENTINEL; it_cl++)
      if (clause_seen(*it_cl)) {
        p_new_comp->addCl(*it_cl);
           if(!clause_all_lits_active(*it_cl))
             current_comp_for_caching_.addCl(*it_cl);
        setClause_in_other_comp(*it_cl);
      }
    p_new_comp->closeClauseData();
    current_comp_for_caching_.closeClauseData();
    return p_new_comp;
  }
//  Component *makeComponentFromState(unsigned stack_size) {
//      Component *p_new_comp = new Component();
//      p_new_comp->reserveSpace(stack_size, super_comp().numLongClauses());
//
//      for (auto v_it = super_comp().varsBegin(); *v_it != varsSENTINEL;  v_it++)
//        if (var_seen(*v_it)) { //we have to put a var into our component
//          p_new_comp->addVar(*v_it);
//          setVar_in_other_comp(*v_it);
//        }
//      p_new_comp->closeVariableData();
//
//      for (auto it_cl = super_comp().clsBegin(); *it_cl != clsSENTINEL; it_cl++)
//        if (clause_seen(*it_cl)) {
//          p_new_comp->addCl(*it_cl);
//          setClause_in_other_comp(*it_cl);
//        }
//      p_new_comp->closeClauseData();
//      return p_new_comp;
//    }

  inline void createComponents(Component &ret_comp, CacheableComponent ret_cache_comp,
      unsigned stack_size);

  Component current_comp_for_caching_;
private:
  Component *p_super_comp_;
  StackLevel *p_stack_level_;

  ComponentArchetypeState* static_state;
  // static CA_SearchState *seen_;
  // static unsigned seen_byte_size_;

};





void ComponentArchetype::createComponents(Component &ret_comp,
      CacheableComponent ret_cache_comp,
      unsigned stack_size){

//      ret_comp.reserveSpace(stack_size, super_comp().numLongClauses());
//      current_comp_for_caching_.clear();
//
//      VariableIndex prev_var = 0;
//      for (auto v_it = super_comp().varsBegin(); *v_it != varsSENTINEL;  v_it++)
//        if (var_seen(*v_it)) { //we have to put a var into our component
//          ret_comp.addVar(*v_it);
//          current_comp_for_caching_.addVar(*v_it - prev_var - 1);
//          prev_var = *v_it;
//          setVar_in_other_comp(*v_it);
//      }
//      ret_comp.closeVariableData();
//      current_comp_for_caching_.closeVariableData();
//
//      ClauseIndex prev_cl = 0;
//      for (auto it_cl = super_comp().clsBegin(); *it_cl != clsSENTINEL; it_cl++)
//        if (clause_seen(*it_cl)) {
//          ret_comp.addCl(*it_cl);
//          if(!clause_all_lits_active(*it_cl)){
//            current_comp_for_caching_.addCl(*it_cl - prev_cl - 1);
//            prev_cl =  *it_cl;
//          }
//          setClause_in_other_comp(*it_cl);
//        }
//      ret_comp.closeClauseData();
//      //current_comp_for_caching_.closeClauseData();
//      return p_new_comp;

}


#endif /* COMPONENT_ARCHETYPE_H_ */
