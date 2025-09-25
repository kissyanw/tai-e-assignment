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
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import static pascal.taie.ir.exp.ArithmeticExp.Op.*;
import static pascal.taie.ir.exp.BitwiseExp.Op.*;
import static pascal.taie.ir.exp.ShiftExp.Op.*;

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
        CPFact boundary = new CPFact();

        for(Var var : cfg.getIR().getVars()){
            if(!canHoldInt(var)){
                boundary.update(var, Value.getUndef());
            }
        }

        for(Var param : cfg.getIR().getParams()){
            if(canHoldInt(param)){
                boundary.update(param, Value.getNAC());
            }
        }

        if (cfg.getIR().getThis() != null && canHoldInt(cfg.getIR().getThis())) {
            boundary.update(cfg.getIR().getThis(), Value.getNAC());
        }

        return boundary;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me

        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for(Var var: fact.keySet()) {
            Value source = fact.get(var);
            Value dest = target.get(var);

            target.update(var, meetValue(source, dest));
        }
    }
    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if(v1.isNAC() || v2.isNAC()) return Value.getNAC();
        else if(v1.isUndef() && v2.isUndef()) return Value.getUndef();
        else if (v1.isUndef() && v2.isConstant()) return v2;
        else if(v1.isConstant() && v2.isUndef()) return v1;
        else if(v1.getConstant() != v2.getConstant()) return Value.getNAC();
        else return Value.makeConstant(v1.getConstant());
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        boolean changed = false;
        CPFact new_out = in.copy();

        if(stmt instanceof DefinitionStmt<?,?> definitionStmt) {
            LValue left = definitionStmt.getLValue();
            RValue right = definitionStmt.getRValue();

            if(left instanceof Var varLeft && canHoldInt(varLeft)) {
                Value valueRight = evaluate(right, new_out);
                if (valueRight != null) new_out.update(varLeft, valueRight);
            }
            //else 恒等处理
        }
        return out.copyFrom(new_out);
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
        if (exp instanceof  IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }
        else if (exp instanceof Var var) {
            return in.get(var);
        }
        else if (exp instanceof BinaryExp binaryExp) {
            Var var1 = binaryExp.getOperand1();
            Var var2 = binaryExp.getOperand2();
            BinaryExp.Op op = binaryExp.getOperator();

            Value v1 = in.get(var1);
            Value v2 = in.get(var2);

            if(v1.isConstant() && v2.isConstant()) {
                int val1 = v1.getConstant();
                int val2 = v2.getConstant();
                if (exp instanceof ArithmeticExp) {
                    switch ((ArithmeticExp.Op) op) {
                        case ADD -> {
                            return Value.makeConstant(val1 + val2);
                        }
                        case SUB -> {
                            return Value.makeConstant(val1 - val2);
                        }
                        case MUL -> {
                            return Value.makeConstant(val1 * val2);
                        }
                        case DIV -> {
                            if (val2 == 0) return Value.getUndef();
                            return Value.makeConstant(val1 / val2);
                        }
                        case REM -> {
                            if (val2 == 0) return Value.getUndef();
                            return Value.makeConstant(val1 % val2);
                        }
                    }
                }
                else if (exp instanceof BitwiseExp) {
                    switch ((BitwiseExp.Op) op) {
                        case AND -> {
                            return Value.makeConstant(val1 & val2);
                        }
                        case OR -> {
                            return Value.makeConstant(val1 | val2);
                        }
                        case XOR -> {
                            return Value.makeConstant(val1 ^ val2);
                        }
                    }
                }
                else if (exp instanceof ShiftExp) {
                    switch ((ShiftExp.Op) op) {
                        case SHL -> {
                            return Value.makeConstant(val1 << val2);
                        }
                        case SHR -> {
                            return Value.makeConstant(val1 >> val2);
                        }
                        case USHR -> {
                            return Value.makeConstant(val1 >>> val2);
                        }
                    }
                }
                else if (exp instanceof ConditionExp) {
                    switch ((ConditionExp.Op) op) {
                        case EQ -> {
                            return Value.makeConstant(val1 == val2 ? 1 : 0);
                        }
                        case NE -> {
                            return Value.makeConstant(val1 != val2 ? 1 : 0);
                        }
                        case LT -> {
                            return Value.makeConstant(val1 < val2 ? 1 : 0);
                        }
                        case LE -> {
                            return Value.makeConstant(val1 <= val2 ? 1 : 0);
                        }
                        case GT -> {
                            return Value.makeConstant(val1 > val2 ? 1 : 0);
                        }
                        case GE -> {
                            return Value.makeConstant(val1 >= val2 ? 1 : 0);
                        }
                    }
                }
            } else if(v1.isNAC() || v2.isNAC()) {
                if(binaryExp instanceof ArithmeticExp) {
                    if(op == DIV || op == REM) {
                        // division by zero may happen
                        if(v2.isConstant() && v2.getConstant() == 0) {
                            return Value.getUndef();
                        }
                    }
                    else return Value.getNAC();
                }
            } else if(v1.isUndef() || v2.isUndef()) {
                return Value.getUndef();
            }
        }
        else return Value.getNAC();

        return null;
    }
}
