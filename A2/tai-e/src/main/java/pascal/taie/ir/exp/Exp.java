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

package pascal.taie.ir.exp;

import pascal.taie.language.type.Type;

import java.util.List;

/**
 * Representation of expressions in Tai-e IR.
 */
public interface Exp {

    /**
     * @return type of this expression.
     */
    Type getType();

    /**
     * @return a list of expressions which are used by (contained in) this Exp.
     * default implementation returns an empty list. (Java 8) The empty list can not be changed. (Java 9)
     */
    default List<RValue> getUses() {
        return List.of();
    }

    /**
     * ExpVisitor is a visitor interface for visiting expressions.
     * it implements a correspond  visit method for each Exp subclass.
     * accept is a method that accepts a visitor and calls the corresponding visit method. which called double dispatch.
     * T is the return type of the visit method.
     */
    <T> T accept(ExpVisitor<T> visitor);
}
