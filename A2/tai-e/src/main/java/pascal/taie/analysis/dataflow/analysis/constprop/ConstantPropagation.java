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

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;
import java.util.Optional;
import java.util.Set;
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
        for(Stmt stmt: cfg) {
            Optional<LValue> lValueOptional = stmt.getDef();
            List<RValue> rValue = stmt.getUses();
            if(lValueOptional.isPresent() && lValueOptional.get() instanceof Var lVar && canHoldInt(lVar)) {
                result.update(lVar, Value.getUndef());
            }
            for(RValue rVal: rValue) {
                if(rVal instanceof Var rVar && canHoldInt(rVar)) {
                    result.update(rVar, Value.getUndef());
                }
            }
        }

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
        Set<Var> keySet = fact.keySet();
        for(Var key: keySet) {
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
        if(result.equals(out)) {
            return false;
        } else {
            // out = result  IT IS WRONG!!!  that statement changes the object "out" points to, but doesn't change the
            // real object we want to change
            out.clear();
            for(Var key: result.keySet()) {
                out.update(key, result.get(key));
            }
            return true;
        }
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
    public static Value evaluate(Exp exp, CPFact in) {
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
                result = Value.getNAC();
            } else {
                result = Value.getUndef();
            }
        } else if(exp instanceof Var var) {
            result = in.get(var);
        } else if(exp instanceof IntLiteral intLiteral) {
            result = Value.makeConstant(intLiteral.getValue());
        } else {
                result = Value.getNAC();
        }
        return result;
    }
}
