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
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;
    public static final HashMap<Pair<Obj, FieldRef>, Value> instanceFieldFact = new HashMap<>();
    public static final HashMap<Pair<Obj, Integer>, Value> arrayFact = new HashMap<>();
    public static final HashMap<Obj, Value> arrayNACFact = new HashMap<>();
    public static final HashMap<Pair<JClass, FieldRef>, Value> staticFieldFact = new HashMap<>();
    public static final HashMap<Pair<JClass, FieldRef>, HashSet<LoadField>> staticFieldLoader = new HashMap<>();
    public static final HashMap<Obj, HashSet<Var>> holding = new HashMap<>();
    public static PointerAnalysisResult pta = null;


    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        // You can do initialization work here
        pta = World.get().getResult(ptaId);
        for(Obj obj: pta.getObjects()) {
            holding.put(obj, new HashSet<>());
        }
        for(Var var: pta.getVars()) {
            for(Obj obj: pta.getPointsToSet(var)) {
                holding.get(obj).add(var);
            }
        }
        for(Stmt stmt: icfg) {
            if(stmt instanceof LoadField loadField && loadField.getFieldAccess() instanceof StaticFieldAccess staticFieldAccess) {
                FieldRef fieldRef = staticFieldAccess.getFieldRef();
                Pair<JClass, FieldRef> pair = new Pair<>(fieldRef.getDeclaringClass(), fieldRef);
                staticFieldLoader.computeIfAbsent(pair, k -> new HashSet<>());
                staticFieldLoader.get(pair).add(loadField);
            }
        }

    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        boolean changed = cp.transferNode(stmt, in, out);

        if(stmt instanceof StoreField storeField && ConstantPropagation.canHoldInt(storeField.getRValue())) {
            if(storeField.getFieldAccess() instanceof StaticFieldAccess staticFieldAccess) {
                FieldRef fieldRef = staticFieldAccess.getFieldRef();
                Pair<JClass, FieldRef> pair = new Pair<>(fieldRef.getDeclaringClass(), fieldRef);
                Value result = cp.meetValue(staticFieldFact.getOrDefault(pair, Value.getUndef()), in.get(storeField.getRValue()));
                if(!result.equals(staticFieldFact.getOrDefault(pair, Value.getUndef()))) {
                    changed = true;
                }
                staticFieldFact.put(pair, result);
            } else if(storeField.getFieldAccess() instanceof InstanceFieldAccess instanceFieldAccess) {
                FieldRef fieldRef = instanceFieldAccess.getFieldRef();
                Var base = instanceFieldAccess.getBase();
                Value newVal = in.get(storeField.getRValue());
                for(Obj obj: pta.getPointsToSet(base)) {
                    Pair<Obj, FieldRef> pair = new Pair<>(obj, fieldRef);
                    Value result = cp.meetValue(instanceFieldFact.getOrDefault(pair, Value.getUndef()), newVal);
                    if(!result.equals(instanceFieldFact.getOrDefault(pair, Value.getUndef()))) {
                        changed = true;
                    }
                    instanceFieldFact.put(pair, result);
                }
            }
        } else if(stmt instanceof StoreArray storeArray && ConstantPropagation.canHoldInt(storeArray.getRValue())) {
            Var base = storeArray.getArrayAccess().getBase();
            Var index = storeArray.getArrayAccess().getIndex();
            Value newVal = in.get(storeArray.getRValue());
            if(in.get(index).isConstant()) {
                Integer idx = in.get(index).getConstant();
                for(Obj obj: pta.getPointsToSet(base)) {
                    Pair<Obj, Integer> pair = new Pair<>(obj, idx);
                    Value result = cp.meetValue(arrayFact.getOrDefault(pair, Value.getUndef()), newVal);
                    if(!result.equals(arrayFact.getOrDefault(pair, Value.getUndef()))) {
                        changed = true;
                    }
                    arrayFact.put(pair, result);
                }
            } else if(in.get(index).isNAC()) {
                for(Obj obj: pta.getPointsToSet(base)) {
                    Value result = cp.meetValue(arrayNACFact.getOrDefault(obj, Value.getUndef()), newVal);
                    if(!result.equals(arrayNACFact.getOrDefault(obj, Value.getUndef()))) {
                        changed = true;
                    }
                    arrayNACFact.put(obj, result);
                }
            }
        }

        return changed;
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact result = out.copy();
        Stmt src = edge.getSource();
        if(src instanceof Invoke invoke) {
            Var var = invoke.getResult();
            if(null != var && ConstantPropagation.canHoldInt(var)) {
                result.remove(var);
            }
        }
        return result;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact result = cp.newInitialFact();
        Stmt src = edge.getSource();
        if(src instanceof Invoke invoke) {
            InvokeExp invokeExp = invoke.getInvokeExp();
            List<Var> args = invokeExp.getArgs();
            List<Var> params = edge.getCallee().getIR().getParams();
            assert args.size() == params.size();
            for(int i = 0; i < args.size(); i++) {
                Var arg = args.get(i);
                Var param = params.get(i);
                if(ConstantPropagation.canHoldInt(param)) {
                    result.update(param, callSiteOut.get(arg));
                }
            }
        }
        return result;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact result = cp.newInitialFact();
        Stmt callSite = edge.getCallSite();
        Collection<Var> returnVars = edge.getReturnVars();
        if(callSite instanceof Invoke invoke) {
            Var override = invoke.getLValue();
            if(null != override && ConstantPropagation.canHoldInt(override)) {
                Value val = Value.getUndef();
                for(Var ret: returnVars) {
                    val = cp.meetValue(val, returnOut.get(ret));
                }
                result.update(override, val);
            }
        }
        return result;
    }
}
