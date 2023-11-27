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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.ReferenceLiteral;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if(callGraph.addReachableMethod(csMethod)) {
            StmtProcessor visitor = new StmtProcessor(csMethod);
            for(Stmt stmt: csMethod.getMethod().getIR().getStmts()) {
                stmt.accept(visitor);
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me


        @Override
        public Void visit(New stmt) {
            CSVar csVar = csManager.getCSVar(context, stmt.getLValue());
            CSObj csObj = csManager.getCSObj(contextSelector.selectHeapContext(csMethod, heapModel.getObj(stmt)), heapModel.getObj(stmt));
            workList.addEntry(csVar, PointsToSetFactory.make(csObj));
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if(stmt.isStatic()) {
                JMethod calledMethod = stmt.getMethodRef().resolve();
                Context ct = contextSelector.selectContext(csManager.getCSCallSite(context, stmt), calledMethod);
                CSMethod calledCSMethod = csManager.getCSMethod(ct, calledMethod);
                if(callGraph.addEdge(new Edge<>(CallKind.STATIC, csManager.getCSCallSite(context, stmt), calledCSMethod))) {
                    addReachable(calledCSMethod);

                    Var lVar = stmt.getLValue();
                    List<Var> args = stmt.getInvokeExp().getArgs();
                    List<Var> params = calledMethod.getIR().getParams();

                    List<Var> retVars = csMethod.getMethod().getIR().getReturnVars();
                    assert args.size() == params.size();

                    for(int i = 0; i < args.size(); i++) {
                        addPFGEdge(csManager.getCSVar(context, args.get(i)), csManager.getCSVar(ct, params.get(i)));
                    }

                    if(null != lVar) {
                        for(Var retVar: retVars) {
                            addPFGEdge(csManager.getCSVar(ct, retVar), csManager.getCSVar(context, lVar));
                        }
                    }
                }

            }
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            CSVar lCSVar = csManager.getCSVar(context, stmt.getLValue());
            CSVar rCSVar = csManager.getCSVar(context, stmt.getRValue());
            addPFGEdge(rCSVar, lCSVar);
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if(stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                CSVar rCSVar = csManager.getCSVar(context, stmt.getRValue());
                addPFGEdge(rCSVar, csManager.getStaticField(field));
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if(stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                CSVar lCSVar = csManager.getCSVar(context, stmt.getLValue());
                addPFGEdge(csManager.getStaticField(field), lCSVar);
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
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());
            if(entry.pointer() instanceof CSVar csVar) {
                for(CSObj csObj: delta) {

                    for(LoadField stmt: csVar.getVar().getLoadFields()) {
                        CSVar lCSVar = csManager.getCSVar(csVar.getContext(), stmt.getLValue());
                        addPFGEdge(csManager.getInstanceField(csObj, stmt.getFieldRef().resolve()), lCSVar);
                    }

                    for(StoreField stmt: csVar.getVar().getStoreFields()) {
                        CSVar rCSVar = csManager.getCSVar(csVar.getContext(), stmt.getRValue());
                        addPFGEdge(rCSVar, csManager.getInstanceField(csObj, stmt.getFieldRef().resolve()));
                    }

                    for(LoadArray stmt: csVar.getVar().getLoadArrays()) {
                        CSVar lCSVar = csManager.getCSVar(csVar.getContext(), stmt.getLValue());
                        addPFGEdge(csManager.getArrayIndex(csObj), lCSVar);
                    }

                    for(StoreArray stmt: csVar.getVar().getStoreArrays()) {
                        CSVar rCSVar = csManager.getCSVar(csVar.getContext(), stmt.getRValue());
                        addPFGEdge(rCSVar, csManager.getArrayIndex(csObj));
                    }

                    processCall(csVar, csObj);
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
        PointsToSet delta = PointsToSetFactory.make();
        pointsToSet.forEach(csObj -> {
            if(!pointer.getPointsToSet().contains(csObj)) {
                delta.addObject(csObj);
            }
        });
        if(!delta.isEmpty()) {
            pointer.getPointsToSet().addAll(delta);
            for(Pointer suc: pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(suc, delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        for(Invoke stmt: recv.getVar().getInvokes()) {
            JMethod method = resolveCallee(recvObj, stmt);
            Context c = recv.getContext();
            Context ct = contextSelector.selectContext(csManager.getCSCallSite(c, stmt), recvObj, method);
            CSMethod csMethod = csManager.getCSMethod(ct, method);
            Var thisVar = method.getIR().getThis();
            // add entry instead of addPFGEdge because not all objs in points-to-set can be the recvObj
            workList.addEntry(csManager.getCSVar(ct, thisVar), PointsToSetFactory.make(recvObj));

            if(callGraph.addEdge(new Edge<>(CallKind.VIRTUAL, csManager.getCSCallSite(c, stmt), csMethod))) {
                addReachable(csMethod);
                List<Var> args = stmt.getInvokeExp().getArgs();
                List<Var> params = method.getIR().getParams();
                assert args.size() == params.size();

                Var lVar = stmt.getLValue();
                List<Var> retVars = method.getIR().getReturnVars();

                for(int i = 0; i < args.size(); i++) {
                    addPFGEdge(csManager.getCSVar(c, args.get(i)), csManager.getCSVar(ct, params.get(i)));
                }

                if(null != lVar) {
                    retVars.forEach(retVar -> addPFGEdge(csManager.getCSVar(ct, retVar), csManager.getCSVar(c, lVar)));
                }
            }


        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
