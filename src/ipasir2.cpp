/******************************************
 * 
 * IPASIR-2 by Markus Iser, 2023
 * 
 * Build upon IPASIR for CryptoMiniSat
 * 
Copyright (c) 2014, Tomas Balyo, Karlsruhe Institute of Technology.
Copyright (c) 2014, Armin Biere, Johannes Kepler University.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to
deal in the Software without restriction, including without limitation the
rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
IN THE SOFTWARE.
***********************************************/

#include "ipasir2.h"
#include "cryptominisat.h"
#include "solverconf.h"
#include "solver.h"
#include <vector>
#include <complex>
#include <cassert>
#include <string.h>
#include "constants.h"

class SolverWrapper {
    CMSat::SolverConf* conf;
    std::atomic<bool> terminate;

    CMSat::Solver* solver;

    std::vector<CMSat::Lit> assumptions;
    std::vector<CMSat::Lit> clause;

    std::vector<uint8_t> is_failed_assumption;

    ipasir2_state state;

    void createVarIfNotExists(int32_t lit) {
        if (abs(lit) > solver->nVars()) {
            solver->new_vars(abs(lit) - solver->nVars());
        }
        if (abs(lit)*2 > is_failed_assumption.size()) {
            is_failed_assumption.resize(abs(lit)*2, 0);
        }
    }

    CMSat::Lit toCMSatLit(int32_t lit) {
        return CMSat::Lit(abs(lit)-1, lit < 0);
    }

public:
    SolverWrapper() : conf(), terminate(), assumptions(), clause(), state(IPASIR2_S_CONFIG) {
        conf = new CMSat::SolverConf();
        solver = nullptr;
    }

    ~SolverWrapper() {
        delete solver;
    }

    CMSat::SolverConf* getConf() {
        return conf;
    }

    ipasir2_state getState() {
        return state;
    }

    void add(int32_t lit) {
        if (state == IPASIR2_S_UNSAT) {
            std::fill(is_failed_assumption.begin(), is_failed_assumption.end(), 0);
        }
        else if (solver == nullptr) {
            solver = new CMSat::Solver(conf, &terminate);
        }
        state = IPASIR2_S_INPUT;
        createVarIfNotExists(lit);
        if (lit == 0) {
            solver->add_clause_outside(clause);
            clause.clear();
        } 
        else {
            clause.push_back(toCMSatLit(lit));
        }
    }

    void assume(int32_t lit) {
        if (state == IPASIR2_S_UNSAT) {
            std::fill(is_failed_assumption.begin(), is_failed_assumption.end(), 0);
        }
        else if (solver == nullptr) {
            solver = new CMSat::Solver(conf, &terminate);
        }
        state = IPASIR2_S_INPUT;
        createVarIfNotExists(lit);
        assumptions.push_back(toCMSatLit(lit));
    }

    int solve() {
        if (solver == nullptr) {
            solver = new CMSat::Solver(conf, &terminate);
            state = IPASIR2_S_SOLVING;
        }
        CMSat::lbool ret = solver->solve_with_assumptions(&assumptions);
        assumptions.clear();
        std::fill(is_failed_assumption.begin(), is_failed_assumption.end(), 0);

        if (ret == CMSat::l_True) {
            state = IPASIR2_S_SAT;
            return 10;
        }
        else if (ret == CMSat::l_False) {
            for (CMSat::Lit failed : solver->get_final_conflict()) {
                is_failed_assumption[failed.toInt()] = 1;
            }
            state = IPASIR2_S_UNSAT;
            return 20;
        }
        else if (ret == CMSat::l_Undef) {
            state = IPASIR2_S_INPUT;
            return 0;
        }
        return -1;
    }

    int val(int32_t lit) {
        if (state != IPASIR2_S_SAT) {
            return 0;
        }
        CMSat::lbool res = solver->get_model()[abs(lit)-1];
        if (res == CMSat::l_True) {
            return lit;
        }
        else if (res == CMSat::l_False) {
            return -lit;
        }
    }

    int failed(int32_t lit) {
        if (state != IPASIR2_S_UNSAT) {
            return 0;
        }
        if (is_failed_assumption[toCMSatLit(-lit).toInt()]) {
            return lit;
        }
        return 0;
    }
};


extern "C" {

    ipasir2_errorcode ipasir2_signature(const char** signature) {
        static char tmp[200];
        std::string tmp2 = "cryptominisat-";
        tmp2 += CMSat::SATSolver::get_version();
        memcpy(tmp, tmp2.c_str(), tmp2.length()+1);
        *signature = tmp;
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_init(void** solver) {
        *solver = (void*)new SolverWrapper();
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_release(void* solver) {
        delete (SolverWrapper*)solver;
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_options(void* solver, ipasir2_option const** options) {
        static std::vector<ipasir2_option> const solver_options = {
            { "branch_strategy_setup", 0, 3, IPASIR2_S_CONFIG, true, false,
                reinterpret_cast<void*>(+[] (SolverWrapper* solver, int64_t value) {
                    switch (value) {
                        case 0: solver->getConf()->branch_strategy_setup.assign("vsids"); break;
                        case 1: solver->getConf()->branch_strategy_setup.assign("vmtf"); break;
                        case 2: solver->getConf()->branch_strategy_setup.assign("rand"); break;
                        case 3: solver->getConf()->branch_strategy_setup.assign("vmtf+vsids"); break;
                    }
                })
            },
            { "varElimRatioPerIter", 10, 100, IPASIR2_S_CONFIG, true, false,
                reinterpret_cast<void*>(+[] (SolverWrapper* solver, int64_t value) { solver->getConf()->varElimRatioPerIter = (double)value / 100; })
            },
            { "restartType", 0, 4, IPASIR2_S_CONFIG, true, false,
                reinterpret_cast<void*>(+[] (SolverWrapper* solver, int64_t value) { solver->getConf()->restartType = CMSat::Restart(value); })
            },
            { "polarity_mode", 0, 7, IPASIR2_S_CONFIG, true, false,
                reinterpret_cast<void*>(+[] (SolverWrapper* solver, int64_t value) { solver->getConf()->polarity_mode = CMSat::PolarityMode(value); })
            },
            { "inc_max_temp_lev2_red_cls", 4, 100, IPASIR2_S_CONFIG, true, false,
                reinterpret_cast<void*>(+[] (SolverWrapper* solver, int64_t value) { solver->getConf()->inc_max_temp_lev2_red_cls = (double)value / 100; })
            },
            { "glue_put_lev0_if_below_or_eq", 0, 4, IPASIR2_S_CONFIG, true, false,
                reinterpret_cast<void*>(+[] (SolverWrapper* solver, int64_t value) { solver->getConf()->glue_put_lev0_if_below_or_eq = value; })
            },
            { "glue_put_lev1_if_below_or_eq", 0, 6, IPASIR2_S_CONFIG, true, false,
                reinterpret_cast<void*>(+[] (SolverWrapper* solver, int64_t value) { solver->getConf()->glue_put_lev1_if_below_or_eq = value; })
            },
            { "every_lev1_reduce", 1, 10000, IPASIR2_S_CONFIG, true, false,
                reinterpret_cast<void*>(+[] (SolverWrapper* solver, int64_t value) { solver->getConf()->every_lev1_reduce = value; })
            },
            { "every_lev2_reduce", 1, 15000, IPASIR2_S_CONFIG, true, false,
                reinterpret_cast<void*>(+[] (SolverWrapper* solver, int64_t value) { solver->getConf()->every_lev2_reduce = value; })
            },
            { "do_bva", 0, 1, IPASIR2_S_CONFIG, true, false,
                reinterpret_cast<void*>(+[] (SolverWrapper* solver, int64_t value) { solver->getConf()->do_bva = value; })
            },
            { "doMinimRedMoreMore", 0, 2, IPASIR2_S_CONFIG, true, false,
                reinterpret_cast<void*>(+[] (SolverWrapper* solver, int64_t value) { solver->getConf()->doMinimRedMoreMore = value; })
            },
            { "max_num_lits_more_more_red_min", 0, 20, IPASIR2_S_CONFIG, true, false,
                reinterpret_cast<void*>(+[] (SolverWrapper* solver, int64_t value) { solver->getConf()->max_num_lits_more_more_red_min = value; })
            },
            { "max_glue_more_minim", 0, 4, IPASIR2_S_CONFIG, true, false,
                reinterpret_cast<void*>(+[] (SolverWrapper* solver, int64_t value) { solver->getConf()->max_glue_more_minim = value; })
            },
            { nullptr, 0, 0, IPASIR2_S_CONFIG, 0, 0, nullptr }
        };

        *options = solver_options.data();
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_set_option(void* solver, ipasir2_option const* opt, int64_t index, int64_t value) {
        SolverWrapper* cms = (SolverWrapper*)solver;
        if (cms->getState() != IPASIR2_S_CONFIG) {
            return IPASIR2_E_INVALID_STATE;    
        }
        if (opt != nullptr) {
            if (value < opt->min || value > opt->max) {
                return IPASIR2_E_INVALID_OPTION_VALUE;
            }
            if (opt->handle != nullptr) {
                void (*setter)(SolverWrapper* solver, int64_t value) = (void (*)(SolverWrapper* solver, int64_t value))opt->handle;
                setter(((SolverWrapper*)solver), value);
                return IPASIR2_E_OK;
            }
            return IPASIR2_E_UNSUPPORTED_OPTION;
        }
        else {
            return IPASIR2_E_INVALID_ARGUMENT;
        }
    }

    ipasir2_errorcode ipasir2_add(void* solver, int32_t const* clause, int32_t len, ipasir2_redundancy type) {
        for (int i = 0; i < len; i++) {
            ((SolverWrapper*)solver)->add(clause[i]);
        }
        ((SolverWrapper*)solver)->add(0);
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_solve(void* solver, int32_t* result, int32_t const* assumps, int32_t len) {
        for (int i = 0; i < len; i++) {
            ((SolverWrapper*)solver)->assume(assumps[i]);
        }
        *result = ((SolverWrapper*)solver)->solve();
        if (*result == -1) {
            return IPASIR2_E_UNKNOWN;
        }
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_val(void* solver, int32_t lit, int32_t* val) {
        *val = ((SolverWrapper*)solver)->val(lit);
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_failed(void* solver, int32_t lit, int32_t* failed) {
        *failed = ((SolverWrapper*)solver)->failed(lit);
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_set_terminate(void* solver, void* state, 
            int (*callback)(void* state)) {
        return IPASIR2_E_UNSUPPORTED;
    }

    ipasir2_errorcode ipasir2_set_export(void* solver, void* state, int32_t max_length,
            void (*callback)(void* state, int32_t const* clause)) {
        return IPASIR2_E_UNSUPPORTED;
    }

    ipasir2_errorcode ipasir2_set_import(void* solver, void* data, ipasir2_redundancy pledge, 
            void (*callback)(void* data, ipasir2_redundancy type)) {
        return IPASIR2_E_UNSUPPORTED;
    }

    ipasir2_errorcode ipasir2_set_notify(void* solver, void* data, 
            void (*callback)(void* data, int32_t const* assigned, int32_t const* unassigned)) {
        return IPASIR2_E_UNSUPPORTED;
    }

}
