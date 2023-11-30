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

package pascal.taie.analysis.dataflow.analysis.constprop;

import jas.Pair;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.dataflow.inter.InterConstantPropagation;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.*;
import java.util.concurrent.ConcurrentHashMap;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact result = new CPFact();

        // Here getParams gets the parameters in function definitions
        // params should be set to NAC because they are not decided until the function is called
        IR ir = cfg.getIR();
        for(Var var: ir.getParams()) {
            if(canHoldInt(var)) {
                result.update(var, Value.getNAC());
            }
        }
        return result;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for(Var key: fact.keySet()) {
            Value val1 = fact.get(key);
            Value val2 = target.get(key);
            // meet value is called here
            target.update(key, meetValue(val1, val2));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        Value result;
        if(v1.isNAC() || v2.isNAC()) { // either is NAC
            result = Value.getNAC();
        } else if(v1.isConstant() && v2.isConstant()) { // both are constants
            if(v1.getConstant() == v2.getConstant()) {
                result = v1;
            } else {
                result = Value.getNAC();
            }
        } else if(v1.isConstant() && v2.isUndef()) { // one UNDEF and one constant
            result = v1;
        } else if(v1.isUndef() && v2.isConstant()) { // one UNDEF and one constant
            result = v2;
        } else { // both UNDEFs
            result = Value.getUndef();
        }
        return result;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact result = in.copy();
        if(stmt instanceof DefinitionStmt<?,?> definitionStmt) { // only takes definitions into account
            LValue lVal = definitionStmt.getLValue();
            RValue rVal = definitionStmt.getRValue();
            if(lVal instanceof Var lVar && canHoldInt(lVar)) {
                // evaluate is called here, evaluate rVal according to IN[s]
                result.update(lVar, evaluate(rVal, in));
            }
        }
        return out.copyFrom(result);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        Value result;
        if(exp instanceof BinaryExp binaryExp) {
            Var op1 = binaryExp.getOperand1();
            Var op2 = binaryExp.getOperand2();
            Value v1 = in.get(op1);
            Value v2 = in.get(op2);
            if(v1.isConstant() && v2.isConstant()) {
                if(binaryExp instanceof ArithmeticExp arithmeticExp) {
                    switch(arithmeticExp.getOperator()) {
                        case ADD -> result = Value.makeConstant(v1.getConstant() + v2.getConstant());
                        case SUB -> result = Value.makeConstant(v1.getConstant() - v2.getConstant());
                        case DIV -> {
                            if(0 != v2.getConstant()) {
                                result = Value.makeConstant(v1.getConstant() / v2.getConstant());
                            } else {
                                result = Value.getUndef();
                            }
                        }
                        case MUL -> result = Value.makeConstant(v1.getConstant() * v2.getConstant());
                        case REM -> {
                            if(0 != v2.getConstant()) {
                                result = Value.makeConstant(v1.getConstant() % v2.getConstant());
                            } else {
                                result = Value.getUndef();
                            }
                        }
                        default -> result = Value.getUndef();
                    }
                } else if(binaryExp instanceof BitwiseExp bitwiseExp) {
                    switch(bitwiseExp.getOperator()) {
                        case OR -> result = Value.makeConstant(v1.getConstant() | v2.getConstant());
                        case AND -> result = Value.makeConstant(v1.getConstant() & v2.getConstant());
                        case XOR -> result = Value.makeConstant(v1.getConstant() ^ v2.getConstant());
                        default -> result = Value.getUndef();
                    }
                } else if(binaryExp instanceof ConditionExp conditionExp) {
                    switch(conditionExp.getOperator()) {
                        case EQ -> {
                            if(v1.getConstant() == v2.getConstant()) {
                                result = Value.makeConstant(1);
                            } else {
                                result = Value.makeConstant(0);
                            }
                        }
                        case GE -> {
                            if(v1.getConstant() >= v2.getConstant()) {
                                result = Value.makeConstant(1);
                            } else {
                                result = Value.makeConstant(0);
                            }
                        }
                        case GT -> {
                            if(v1.getConstant() > v2.getConstant()) {
                                result = Value.makeConstant(1);
                            } else {
                                result = Value.makeConstant(0);
                            }
                        }
                        case LE -> {
                            if(v1.getConstant() <= v2.getConstant()) {
                                result = Value.makeConstant(1);
                            } else {
                                result = Value.makeConstant(0);
                            }
                        }
                        case LT -> {
                            if(v1.getConstant() < v2.getConstant()) {
                                result = Value.makeConstant(1);
                            } else {
                                result = Value.makeConstant(0);
                            }
                        }
                        case NE -> {
                            if(v1.getConstant() != v2.getConstant()) {
                                result = Value.makeConstant(1);
                            } else {
                                result = Value.makeConstant(0);
                            }
                        }
                        default -> result = Value.getUndef();
                    }
                } else if(binaryExp instanceof ShiftExp shiftExp) {
                    switch (shiftExp.getOperator()) {
                        case SHL -> result = Value.makeConstant(v1.getConstant() << v2.getConstant());
                        case SHR -> result = Value.makeConstant(v1.getConstant() >> v2.getConstant());
                        case USHR -> result = Value.makeConstant(v1.getConstant() >>> v2.getConstant());
                        default -> result = Value.getUndef();
                    }
                } else {
                    result = Value.getUndef();
                }
            } else if(v1.isNAC() || v2.isNAC()) {
                if(exp instanceof ArithmeticExp arithmeticExp && (arithmeticExp.getOperator() == ArithmeticExp.Op.DIV ||
                        arithmeticExp.getOperator() == ArithmeticExp.Op.REM)) {
                    if(v2.isConstant() && 0 == v2.getConstant()) { // when divided by 0, always return Undef
                        result = Value.getUndef();
                    } else {
                        result = Value.getNAC();
                    }
                } else {
                    result = Value.getNAC();
                }
            } else {
                result = Value.getUndef();
            }
        } else if(exp instanceof Var var) {
            result = in.get(var);
        } else if(exp instanceof IntLiteral intLiteral) {
            result = Value.makeConstant(intLiteral.getValue());
        } else if(exp instanceof InstanceFieldAccess instanceFieldAccess) {
            result = Value.getUndef();
            Var base = instanceFieldAccess.getBase();
            for(Obj obj: InterConstantPropagation.pta.getPointsToSet(base)) {
                Pair<Obj, FieldRef> pair = new Pair<>(obj, instanceFieldAccess.getFieldRef());
                result = meetValue(result, InterConstantPropagation.instanceFieldFact.getOrDefault(pair, Value.getUndef()));
            }
        } else if(exp instanceof StaticFieldAccess staticFieldAccess) {
            FieldRef fieldRef = staticFieldAccess.getFieldRef();
            Pair<JClass, FieldRef> pair = new Pair<>(fieldRef.getDeclaringClass(), fieldRef);
            result = InterConstantPropagation.staticFieldFact.getOrDefault(pair, Value.getUndef());

        } else if(exp instanceof ArrayAccess arrayAccess) {
            Var base = arrayAccess.getBase();
            Var index = arrayAccess.getIndex();
            if(in.get(index).isUndef()) {
                result = Value.getUndef();
            } else if(in.get(index).isNAC()) {
                result = Value.getUndef();
                for(Obj obj: InterConstantPropagation.pta.getPointsToSet(base)) {
                    result = meetValue(result, InterConstantPropagation.arrayNACFact.getOrDefault(obj, Value.getUndef()));
                    for(Pair<Obj, Integer> pair: InterConstantPropagation.arrayFact.keySet()) {
                        if(pair.getO1().equals(obj)) {
                            result = meetValue(result, InterConstantPropagation.arrayFact.getOrDefault(pair, Value.getUndef()));
                        }
                    }
                }
            } else {
                result = Value.getUndef();
                for(Obj obj: InterConstantPropagation.pta.getPointsToSet(base)) {
                    Pair<Obj, Integer> pair = new Pair<>(obj, in.get(index).getConstant());
                    result = meetValue(result, InterConstantPropagation.arrayFact.getOrDefault(pair, Value.getUndef()));
                    result = meetValue(result, InterConstantPropagation.arrayNACFact.getOrDefault(obj, Value.getUndef()));
                }
            }
        } else {
            result = Value.getNAC();
        }
        return result;
    }
}
