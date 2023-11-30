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

package pascal.taie.analysis.dataflow.inter;

import jas.Pair;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JClass;
import pascal.taie.util.collection.SetQueue;

import java.util.Queue;
import java.util.Set;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        workList = new ConcurrentLinkedQueue<>();

        Stream<Method> entries = icfg.entryMethods();

        for(Node node: icfg) {
            result.setOutFact(node, analysis.newInitialFact());
            result.setInFact(node, analysis.newInitialFact());
        }

        entries.forEach(entry -> result.setOutFact(icfg.getEntryOf(entry),
                analysis.newBoundaryFact(icfg.getEntryOf(entry))));
    }

    @SuppressWarnings("unchecked")
    private void doSolve() {
        // TODO - finish me
        workList.addAll(icfg.getNodes());
        while(!workList.isEmpty()) {
            Node now = workList.remove();
            for(ICFGEdge<Node> edge: icfg.getInEdgesOf(now)) {
                Node pre = edge.getSource();
                analysis.meetInto(analysis.transferEdge(edge, result.getOutFact(pre)), result.getInFact(now));
            }

            if(analysis.transferNode(now, result.getInFact(now), result.getOutFact(now))) {
                for(Node suc: icfg.getSuccsOf(now)) {
                    if(!workList.contains(suc)) {
                        workList.add(suc);
                    }
                }
            }
            if(now instanceof StoreField storeField) {
                if(storeField.getFieldAccess() instanceof StaticFieldAccess staticFieldAccess) {
                    FieldRef fieldRef = staticFieldAccess.getFieldRef();
                    Pair<JClass, FieldRef> pair = new Pair<>(fieldRef.getDeclaringClass(), fieldRef);
                    for(LoadField loadField: InterConstantPropagation.staticFieldLoader.get(pair)) {
                        workList.add((Node) loadField);
                    }
                } else if(storeField.getFieldAccess() instanceof InstanceFieldAccess instanceFieldAccess) {
                    Var base = instanceFieldAccess.getBase();
                    for(Obj obj: InterConstantPropagation.pta.getPointsToSet(base)) {
                        for(Var var: InterConstantPropagation.holding.get(obj)) {
                            for(LoadField loadField: var.getLoadFields()) {
                                workList.add((Node) loadField);
                            }
                        }
                    }
                }
            } else if(now instanceof StoreArray storeArray) {
                Var base = storeArray.getArrayAccess().getBase();
                for(Obj obj: InterConstantPropagation.pta.getPointsToSet(base)) {
                    for(Var var: InterConstantPropagation.holding.get(obj)) {
                        for(LoadArray loadArray: var.getLoadArrays()) {
                            workList.add((Node) loadArray);
                        }
                    }
                }
            }
        }
    }
}
