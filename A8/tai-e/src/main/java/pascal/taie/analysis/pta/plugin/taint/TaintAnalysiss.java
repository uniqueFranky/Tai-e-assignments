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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

class MethodInvoke {
    public Obj recvObj;
    public CSCallSite csCallSite;
    public CSMethod csMethod;
    public CSVar csVar;
    MethodInvoke(Obj recvObj, CSCallSite csCallSite, CSMethod csMethod, CSVar csVar) {
        this.recvObj = recvObj;
        this.csCallSite = csCallSite;
        this.csMethod = csMethod;
        this.csVar = csVar;
    }

    @Override
    public String toString() {
        if(recvObj != null) {
            return recvObj.toString() + csCallSite.toString() + csMethod.toString();
        }
        return csCallSite.toString() + csMethod.toString();
    }
}

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private final Set<TaintFlow> taintFlows = new TreeSet<>();

    private final Set<MethodInvoke> methodInvokeSet = new HashSet<>();

    public boolean canBeTransferred(CSMethod csMethod, int index) {
        for(TaintTransfer taintTransfer: config.getTransfers()) {
            if(taintTransfer.method().equals(csMethod.getMethod())) {
                if(taintTransfer.from() == index) {
                    return true;
                }
            }
        }
        return false;
    }

    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }

    public void processCall(CSVar recv, Obj recvObj, CSCallSite csCallSite, CSMethod csMethod) {
        methodInvokeSet.add(new MethodInvoke(recvObj, csCallSite, csMethod, recv));
        for(Source source: config.getSources()) {
            if(source.method().equals(csMethod.getMethod())) {
                Obj taint = manager.makeTaint(csCallSite.getCallSite(), source.type());
                Var var = csCallSite.getCallSite().getLValue();
                if(null != var) {
                    CSVar csVar = csManager.getCSVar(csCallSite.getContext(), var);
                    solver.addToWorkList(csVar, csManager.getCSObj(emptyContext, taint));
                }
            }
        }

        for(TaintTransfer taintTransfer: config.getTransfers()) {
            if(taintTransfer.method().equals(csMethod.getMethod())) {
                CSVar from, to;
                if(-1 == taintTransfer.to()) { // to base
                    to = recv;
                } else { // to result
                    to = csManager.getCSVar(csCallSite.getContext(), csCallSite.getCallSite().getLValue());
                }
                if(null == to) {
                    continue;
                }
                if(-1 == taintTransfer.from() && null != recv) { // from base

                    if(manager.isTaint(recvObj)) {
                        System.out.println("from base!!!!!" + recv);

                        Obj taint = manager.makeTaint(manager.getSourceCall(recvObj), taintTransfer.type());
                        solver.addToWorkList(to, csManager.getCSObj(emptyContext, taint));
                    }
                } else if(taintTransfer.from() >= 0) { // from arguments
                    from = csManager.getCSVar(csCallSite.getContext(), csCallSite.getCallSite().getInvokeExp().getArg(taintTransfer.from()));
                    for(CSObj csObj: from.getPointsToSet()) {
                        if(manager.isTaint(csObj.getObject())) {
                            Obj taint = manager.makeTaint(manager.getSourceCall(csObj.getObject()), taintTransfer.type());
                            if(!to.getPointsToSet().contains(csManager.getCSObj(emptyContext, taint))) {
                                solver.addToWorkList(to, csManager.getCSObj(emptyContext, taint));
                            }
                        }
                    }
                }
            }
        }

    }

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        for(MethodInvoke methodInvoke: methodInvokeSet) {
            for(Sink sink: config.getSinks()) {
                if(sink.method().equals(methodInvoke.csMethod.getMethod())) {
                    assert sink.index() >= 0;
                    Var var = methodInvoke.csCallSite.getCallSite().getInvokeExp().getArg(sink.index());
                    CSVar csVar = csManager.getCSVar(methodInvoke.csCallSite.getContext(), var);
                    for(CSObj csObj: csVar.getPointsToSet()) {
                        if(manager.isTaint(csObj.getObject())) {
                            taintFlows.add(new TaintFlow(manager.getSourceCall(csObj.getObject()),
                                    methodInvoke.csCallSite.getCallSite(), sink.index()));
                        }
                    }
                }
            }
        }
        return taintFlows;
    }
}
