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

package pascal.taie.analysis.pta.ci;

import fj.P;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.lang.reflect.Field;
import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if(callGraph.addReachableMethod(method)) {
            for(Stmt stmt: method.getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }

    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me


        @Override
        public Void visit(New stmt) {
            Var var = stmt.getLValue();
            Obj obj = heapModel.getObj(stmt);
            Pointer ptr = pointerFlowGraph.getVarPtr(var);
            workList.addEntry(ptr, new PointsToSet(obj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Var lVar = stmt.getLValue();
            Var rVar = stmt.getRValue();
            Pointer lPtr = pointerFlowGraph.getVarPtr(lVar);
            Pointer rPtr = pointerFlowGraph.getVarPtr(rVar);
            addPFGEdge(rPtr, lPtr);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if(stmt.isStatic()) { // only process static load field
                JField field = stmt.getFieldRef().resolve();
                Var lVar = stmt.getLValue();
                Pointer fPtr = pointerFlowGraph.getStaticField(field);
                Pointer vPtr = pointerFlowGraph.getVarPtr(lVar);
                addPFGEdge(fPtr, vPtr);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if(stmt.isStatic()) { // only process static store field
                JField field = stmt.getFieldRef().resolve();
                Var rVar = stmt.getRValue();
                Pointer fPtr = pointerFlowGraph.getStaticField(field);
                Pointer vPtr = pointerFlowGraph.getVarPtr(rVar);
                addPFGEdge(vPtr, fPtr);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if(stmt.isStatic()) { // only process static invoke
                Var lVar = stmt.getLValue();
                JMethod method = stmt.getMethodRef().resolve();

                addReachable(method);

                List<Var> retVars = method.getIR().getReturnVars();
                List<Var> params = method.getIR().getParams();
                List<Var> args = stmt.getInvokeExp().getArgs();

                assert args.size() == params.size();
                for(int i = 0; i < args.size(); i++) { // pass arguments to parameters
                    addPFGEdge(pointerFlowGraph.getVarPtr(args.get(i)), pointerFlowGraph.getVarPtr(params.get(i)));
                }

                if(null != lVar) {
                    for(Var retVar: retVars) { // pass return vars to call site var
                        addPFGEdge(pointerFlowGraph.getVarPtr(retVar), pointerFlowGraph.getVarPtr(lVar));
                    }
                }

            }
            return null;
        }

    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(pointerFlowGraph.addEdge(source, target)) {
            if(!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }

    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()) {
            WorkList.Entry ent = workList.pollEntry();
            PointsToSet delta = propagate(ent.pointer(), ent.pointsToSet());
            if(ent.pointer() instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();
                for(Obj obj: delta) {
                    for(LoadField loadField: var.getLoadFields()) {
                        JField field = loadField.getFieldRef().resolve();
                        Pointer lPtr = pointerFlowGraph.getVarPtr(loadField.getLValue());
                        Pointer rPtr = pointerFlowGraph.getInstanceField(obj, field);
                        addPFGEdge(rPtr, lPtr);
                    }
                    for(StoreField storeField: var.getStoreFields()) {
                        JField field = storeField.getFieldRef().resolve();
                        Pointer lPtr = pointerFlowGraph.getInstanceField(obj, field);
                        Pointer rPtr = pointerFlowGraph.getVarPtr(storeField.getRValue());
                        addPFGEdge(rPtr, lPtr);
                    }
                    for(LoadArray loadArray: var.getLoadArrays()) {
                        Pointer lPtr = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                        Pointer rPtr = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(rPtr, lPtr);
                    }
                    for(StoreArray storeArray: var.getStoreArrays()) {
                        Pointer lPtr = pointerFlowGraph.getArrayIndex(obj);
                        Pointer rPtr = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                        addPFGEdge(rPtr, lPtr);
                    }
                    processCall(var, obj);
                }
            }

        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet delta = new PointsToSet();
        for(Obj obj: pointsToSet) {
            if(pointer.getPointsToSet().addObject(obj)) {
                delta.addObject(obj);
            }
        }
        if(!delta.isEmpty()) {
            for(Pointer sucPtr: pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(sucPtr, delta);
            }
        }

        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for(Invoke invoke: var.getInvokes()) {
            JMethod callee = resolveCallee(recv, invoke);

            // pass this
            Var thisVar = callee.getIR().getThis();
            workList.addEntry(pointerFlowGraph.getVarPtr(thisVar), new PointsToSet(recv));

            if(callGraph.addEdge(new Edge<>(CallKind.VIRTUAL, invoke, callee))) {
                addReachable(callee);
                List<Var> params = callee.getIR().getParams();
                List<Var> args = invoke.getInvokeExp().getArgs();
                assert params.size() == args.size();

                // pass arguments
                for(int i = 0; i < params.size(); i++) {
                    addPFGEdge(pointerFlowGraph.getVarPtr(args.get(i)),
                            pointerFlowGraph.getVarPtr(params.get(i)));
                }

                // pass return vars
                if(null != invoke.getLValue()) {
                    for(Var retVar: callee.getIR().getReturnVars()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(retVar),
                                pointerFlowGraph.getVarPtr(invoke.getLValue()));
                    }
                }

            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
