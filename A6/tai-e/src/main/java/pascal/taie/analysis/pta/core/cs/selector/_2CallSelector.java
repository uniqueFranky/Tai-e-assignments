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

package pascal.taie.analysis.pta.core.cs.selector;

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.ListContext;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

/**
 * Implementation of 2-call-site sensitivity.
 */
public class _2CallSelector implements ContextSelector {

    @Override
    public Context getEmptyContext() {
        return ListContext.make();
    }

    private Context makeContext(CSCallSite callSite) {
        Context c = callSite.getContext();
        if(0 == c.getLength()) {
            return ListContext.make(callSite.getCallSite());
        } else if(1 == c.getLength()) {
            return ListContext.make(c.getElementAt(0), callSite.getCallSite());
        } else {
            return ListContext.make(c.getElementAt(1), callSite.getCallSite());
        }
    }

    @Override
    public Context selectContext(CSCallSite callSite, JMethod callee) {
        // TODO - finish me
        // static call
        return makeContext(callSite);
    }

    @Override
    public Context selectContext(CSCallSite callSite, CSObj recv, JMethod callee) {
        // TODO - finish me
        return makeContext(callSite);
    }

    @Override
    public Context selectHeapContext(CSMethod method, Obj obj) {
        // TODO - finish me
        Context c = method.getContext();
        if(0 == c.getLength()) {
            return ListContext.make();
        } else if(1 == c.getLength()) {
            return c;
        } else {
            return ListContext.make(c.getElementAt(1));
        }
    }
}
