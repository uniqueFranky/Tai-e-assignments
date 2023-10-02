/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;

import java.util.*;
import java.util.concurrent.ConcurrentLinkedQueue;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        // Control Flow Unreachable
        analyzeControlFlowUnreachable(cfg, deadCode, ir);

        // If Branch Unreachable
        analyzeIfStmtUnreachable(cfg, deadCode, constants);

        // Switch Branch Unreachable
        analyzeSwitchStmtUnreachable(cfg, deadCode, constants);

        // Propagate Unreachable Control Flow
        propagateUnreachable(cfg, deadCode);

        // Useless Assignment
        analyzeUselessAssignment(cfg, deadCode, liveVars);

        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }

    private void analyzeControlFlowUnreachable(CFG<Stmt> cfg, Set<Stmt> deadCode, IR ir) {
        Set<Stmt> controlFlowReachable = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Queue<Stmt> q = new ConcurrentLinkedQueue<>();
        q.add(cfg.getEntry());
        while(!q.isEmpty()) {
            Stmt now = q.remove();
            controlFlowReachable.add(now);
            for(Stmt suc: cfg.getSuccsOf(now)) {
                if(!q.contains(suc) && !controlFlowReachable.contains(suc)) {
                    q.add(suc);
                }
            }
        }
        for(Stmt stmt: ir.getStmts()) {
            if(!controlFlowReachable.contains(stmt)) {
                deadCode.add(stmt);
            }
        }
    }

    private void analyzeIfStmtUnreachable(CFG<Stmt> cfg, Set<Stmt> deadCode, DataflowResult<Stmt, CPFact> constants) {
        for(Stmt stmt: cfg) {
            if(stmt instanceof If ifStmt) {
                Var lVar = ifStmt.getCondition().getOperand1();
                Var rVar = ifStmt.getCondition().getOperand2();
                ConditionExp.Op op = ifStmt.getCondition().getOperator();
                if(constants.getOutFact(ifStmt).get(lVar).isConstant() && constants.getOutFact(ifStmt).get(rVar).isConstant()) {
                    int v1 = constants.getOutFact(ifStmt).get(lVar).getConstant();
                    int v2 = constants.getOutFact(ifStmt).get(rVar).getConstant();
                    boolean eval = evaluateOp(v1, v2, op);
                    for(Edge<Stmt> edge: cfg.getOutEdgesOf(ifStmt)) {
                        if(Edge.Kind.IF_TRUE == edge.getKind() && !eval) {
                            deadCode.add(edge.getTarget());
                        } else if(Edge.Kind.IF_FALSE == edge.getKind() && eval) {
                            deadCode.add(edge.getTarget());
                        }
                    }
                }
            }
        }
    }

    private void analyzeSwitchStmtUnreachable(CFG<Stmt> cfg, Set<Stmt> deadCode, DataflowResult<Stmt, CPFact> constants) {
        for(Stmt stmt: cfg) {
            if(stmt instanceof SwitchStmt switchStmt) {
                Var var = switchStmt.getVar();
                if(constants.getOutFact(stmt).get(var).isConstant()) {
                    boolean match = false;
                    Stmt matchStmt = null;
                    int v = constants.getOutFact(stmt).get(var).getConstant();
                    for(Pair<Integer, Stmt> pair :switchStmt.getCaseTargets()) {
                        if(v != pair.first()) {
                            deadCode.add(pair.second());
                        } else {
                            match = true;
                            matchStmt = pair.second();;
                        }
                    }
                    if(match) { // if any case is matched, default is unreachable
                        deadCode.add(switchStmt.getDefaultTarget());
                        recoverFallThrough(cfg, matchStmt, deadCode); // handle fall through cases
                    }
                }
            }
        }
    }

    private void analyzeUselessAssignment(CFG<Stmt> cfg, Set<Stmt> deadCode, DataflowResult<Stmt, SetFact<Var>> liveVars) {
        for(Stmt stmt: cfg) {
            if(stmt instanceof AssignStmt<?,?> assignStmt) {
                LValue lVal = assignStmt.getLValue();
                RValue rVal = assignStmt.getRValue();
                if(hasNoSideEffect(rVal) && lVal instanceof Var lvar && !liveVars.getOutFact(assignStmt).contains(lvar)) {
                    deadCode.add(assignStmt);
                }
            }
        }
    }

    private void propagateUnreachable(CFG<Stmt> cfg, Set<Stmt> deadCode) {
        Queue<Stmt> q = new ConcurrentLinkedQueue<>(deadCode);
        while(!q.isEmpty()) {
            Stmt now = q.remove();
            deadCode.add(now);
            for(Stmt suc: cfg.getSuccsOf(now)) {
                boolean unreachable = true;
                for(Stmt sucPre: cfg.getPredsOf(suc)) {
                    if(!deadCode.contains(sucPre)) {
                        unreachable = false;
                        break;
                    }
                }
                if(unreachable && !cfg.isExit(suc)) { // exclude exit
                    if(!q.contains(suc) && !deadCode.contains(suc)) {
                        q.add(suc);
                    }
                }
            }
        }
    }

    private void recoverFallThrough(CFG<Stmt> cfg, Stmt stmt, Set<Stmt> deadCode) {
        Queue<Stmt> q = new ConcurrentLinkedQueue<>();
        Set<Stmt> visit = new HashSet<>();
        q.add(stmt);
        while(!q.isEmpty()) {
            Stmt now = q.remove();
            visit.add(now);
            for(Stmt suc: cfg.getSuccsOf(now)) {
                deadCode.remove(suc);
                if(!visit.contains(suc)) {
                    q.add(suc);
                }
            }
        }
    }

    private boolean evaluateOp(int v1, int v2, ConditionExp.Op op) {
        switch(op) {
            case NE -> {
                return v1 != v2;
            }
            case LT -> {
                return v1 < v2;
            }
            case LE -> {
                return v1 <= v2;
            }
            case GT -> {
                return v1 > v2;
            }
            case GE -> {
                return v1 >= v2;
            }
            case EQ -> {
                return v1 == v2;
            }
        }
        return false;
    }

}
