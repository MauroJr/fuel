/**
 * The MIT License (MIT)
 * Copyright (c) Taketoshi Aono
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * @fileoverview
 * @author Taketoshi Aono
 */
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
var type_1 = require("./type");
var node_1 = require("./node");
var tree_1 = require("./tree");
var element_1 = require("./element");
var difference_1 = require("./difference");
var util_1 = require("./util");
function createStem() {
    return new FuelStem();
}
function replaceElement(root, parent, oldElement, newElement, isKeyedItems, renderer) {
    var newDom = element_1.FuelElementView.createDomElement(root, newElement, renderer, createStem);
    var oldDom = oldElement.dom;
    if (oldDom.nodeType === 1 && newDom.nodeType === 1) {
        var children = oldDom.children;
        while (children.length) {
            newDom.appendChild(children[0]);
        }
    }
    var parentDom = parent.dom;
    if (!isKeyedItems) {
        parentDom.replaceChild(newDom, oldDom);
    }
    else {
        parentDom.removeChild(oldDom);
        parentDom.appendChild(newDom);
    }
}
function copyElementRef(root, oldElement, newElement, isKeyedItem) {
    newElement.dom = oldElement.dom;
    element_1.FuelElementView.attachFuelElementToNode(newElement.dom, newElement);
    if (isKeyedItem) {
        newElement.dom.parentNode.appendChild(newElement.dom);
    }
}
function updateElement(diff, rootElement, newElement) {
    var domElement = newElement.dom;
    var strippedRoot = element_1.FuelElementView.stripComponent(rootElement);
    for (var i = 0, len = diff.attr.length; i < len; i++) {
        var _a = diff.attr[i], key = _a.key, value = _a.value, state = _a.state;
        switch (state) {
            case 1 /* NEW */:
            case 3 /* REPLACED */:
                if (type_1.DOMEvents[key]) {
                    var lowerKey = key.slice(2).toLowerCase();
                    strippedRoot._stem.getEventHandler().replaceEvent(newElement.dom, lowerKey, value);
                }
                else {
                    domElement[key] = value;
                }
                break;
            case 5 /* STYLE_CHANGED */:
                for (var style in value) {
                    var val = value[style];
                    node_1.setStyle(domElement, style, val);
                }
                break;
            case 2 /* REMOVED */:
                if (type_1.DOMEvents[key]) {
                    var lowerKey = key.slice(2).toLowerCase();
                    strippedRoot._stem.getEventHandler().removeEvent(newElement.dom, lowerKey);
                }
                else {
                    domElement.removeAttribute(key);
                }
            default:
        }
    }
}
function update(batches) {
    var renderer = FuelStem.renderer;
    for (var i = 0, len = batches.length; i < len; i++) {
        var _a = batches[i], parent_1 = _a.parent, newElement = _a.newElement, oldElement = _a.oldElement, isKeyedItem = _a.isKeyedItem, difference = _a.difference, root = _a.root, context_1 = _a.context;
        if (difference_1.isNewElement(difference)) {
            if (parent_1) {
                parent_1.dom.appendChild(tree_1.fastCreateDomTree(context_1, root, newElement, renderer, createStem));
                element_1.FuelElementView.invokeDidMount(newElement);
            }
            else {
                var tree = tree_1.fastCreateDomTree(context_1, root, newElement, renderer, createStem);
                if (oldElement) {
                    parent_1.dom.appendChild(tree);
                    element_1.FuelElementView.invokeDidMount(newElement);
                    element_1.FuelElementView.invokeWillUnmount(oldElement);
                }
            }
        }
        else if (difference_1.isRemoveElement(difference)) {
            element_1.FuelElementView.invokeWillUnmount(oldElement);
            oldElement.dom.parentNode.removeChild(oldElement.dom);
            oldElement._stem = null;
        }
        else if (difference_1.isReplaceElement(difference)) {
            element_1.FuelElementView.invokeWillUnmount(oldElement);
            replaceElement(root, parent_1, oldElement, newElement, isKeyedItem, renderer);
            element_1.FuelElementView.invokeDidMount(newElement);
        }
        else if (difference_1.isTextChanged(difference)) {
            newElement.dom = oldElement.dom;
            element_1.FuelElementView.attachFuelElementToNode(newElement.dom, newElement);
            newElement.dom.textContent = element_1.FuelElementView.getTextValueOf(newElement);
            element_1.FuelElementView.invokeDidUpdate(newElement);
        }
        else {
            copyElementRef(root, oldElement, newElement, isKeyedItem);
            updateElement(difference, root, newElement);
            element_1.FuelElementView.invokeDidUpdate(newElement);
        }
        if (difference_1.isCreateChildren(difference)) {
            tree_1.fastCreateDomTree(context_1, root, newElement, renderer, createStem);
        }
    }
}
function makeInitialStackState(context, newElement, oldElement) {
    return [
        {
            newElement: newElement,
            oldElement: oldElement,
            newChildren: null,
            oldChildren: null,
            parsed: false,
            difference: null,
            context: context,
            root: newElement,
            isKeyedItem: false
        }
    ];
}
function createNextStackState(context, parentState, prev, oldElement) {
    var newChild = prev.newChildren.shift();
    var oldChild;
    var isKeyedItem = false;
    if (parentState) {
        var parentNewElement = parentState.newElement, parentOldElement = parentState.oldElement;
        if (parentOldElement && parentOldElement._keymap && newChild && parentOldElement._keymap[newChild.key]) {
            oldChild = parentOldElement._keymap[newChild.key];
            if (parentNewElement && !parentNewElement._keymap) {
                parentNewElement._keymap = {};
                parentNewElement._keymap[newChild.key] = newChild;
            }
            var index = prev.oldChildren.indexOf(oldChild);
            if (index !== -1) {
                prev.oldChildren.splice(index, 1);
                isKeyedItem = true;
            }
            else {
                oldChild = prev.oldChildren.shift();
                isKeyedItem = false;
            }
        }
        else {
            oldChild = prev.oldChildren.shift();
            isKeyedItem = false;
        }
    }
    else {
        oldChild = prev.oldChildren.shift();
        isKeyedItem = false;
    }
    var root = prev.root;
    if (newChild) {
        if (newChild._unmounted) {
            newChild = null;
        }
        else if (newChild._stem) {
            root = newChild;
        }
    }
    if (newChild && !newChild._ownerElement) {
        newChild._ownerElement = prev.newElement._ownerElement;
    }
    return {
        newElement: newChild,
        oldElement: oldChild,
        newChildren: null,
        oldChildren: null,
        parsed: false,
        difference: null,
        root: root,
        context: context,
        isKeyedItem: isKeyedItem
    };
}
function patchComponent(context, newElement, oldElement) {
    if (newElement && element_1.FuelElementView.isComponent(newElement)) {
        if (oldElement && oldElement.type !== newElement.type) {
            while (newElement && element_1.FuelElementView.isComponent(newElement)) {
                _a = element_1.FuelElementView.instantiateComponent(context, newElement), newElement = _a[0], context = _a[1];
            }
        }
        else {
            while (newElement && element_1.FuelElementView.isComponent(newElement)) {
                if (newElement && oldElement && newElement.type === oldElement.type) {
                    newElement._componentInstance = oldElement._componentInstance;
                }
                var revealedOldElement = oldElement;
                if (oldElement && element_1.FuelElementView.isComponent(oldElement)) {
                    revealedOldElement = element_1.FuelElementView.getComponentRenderedTree(oldElement);
                }
                var _b = element_1.FuelElementView.instantiateComponent(context, newElement, oldElement), stripedNewTree = _b[0], newContext = _b[1];
                context = newContext;
                oldElement = revealedOldElement;
                newElement = stripedNewTree;
            }
        }
    }
    if (oldElement && element_1.FuelElementView.isComponent(oldElement)) {
        oldElement = element_1.FuelElementView.stripComponent(oldElement);
    }
    return [context, newElement, oldElement];
    var _a;
}
var FuelStem = (function () {
    function FuelStem(tree) {
        if (tree === void 0) { tree = null; }
        this.tree = tree;
        this._enabled = true;
        this.batchs = [];
        this.batchCallback = null;
        this.lock = false;
        this.renderQueue = [];
    }
    FuelStem.prototype.enterUnsafeUpdateZone = function (cb) {
        this._enabled = false;
        cb();
        this._enabled = true;
    };
    FuelStem.prototype.registerOwner = function (owner) {
        this.tree = owner;
    };
    FuelStem.prototype.owner = function () {
        return this.tree;
    };
    FuelStem.prototype.setEventHandler = function (handler) {
        this.sharedEventHandler = handler;
    };
    FuelStem.prototype.getEventHandler = function () {
        return this.sharedEventHandler;
    };
    FuelStem.prototype.renderAtAnimationFrame = function () {
        //    requestAnimationFrame(() => {
        if (this.batchs.length) {
            update(this.batchs);
            this.batchs.length = 0;
            this.batchCallback && this.batchCallback();
            this.batchCallback = null;
        }
        //    });
    };
    FuelStem.prototype.drainRenderQueue = function () {
        var next = this.renderQueue.shift();
        if (next) {
            var element = next.element, cb = next.cb;
            this.render(element, cb);
        }
    };
    FuelStem.prototype.unmountComponent = function (fuelElement, cb) {
        tree_1.cleanupTree(fuelElement, cb);
    };
    FuelStem.prototype.render = function (el, callback, context, updateOwnwer) {
        var _this = this;
        if (callback === void 0) { callback = (function (el) { }); }
        if (context === void 0) { context = {}; }
        if (updateOwnwer === void 0) { updateOwnwer = true; }
        if (!this._enabled) {
            callback(this.tree.dom);
            return;
        }
        if (this.lock) {
            this.renderQueue.push({ element: el, cb: callback });
            return;
        }
        FuelStem.renderer.updateId();
        if (this.tree) {
            this.lock = true;
            this.patch(el, context);
            var old_1 = this.tree;
            if (updateOwnwer) {
                this.tree = el;
            }
            this.batchCallback = function () {
                tree_1.cleanupTree(old_1);
                callback(_this.tree.dom);
                _this.lock = false;
                _this.drainRenderQueue();
            };
            this.renderAtAnimationFrame();
        }
        else {
            callback(this.attach(el, updateOwnwer));
        }
    };
    FuelStem.prototype.attach = function (el, updateOwner) {
        var domTree = tree_1.fastCreateDomTree({}, el, el, FuelStem.renderer, createStem);
        if (updateOwner) {
            this.tree = el;
        }
        return domTree;
    };
    FuelStem.prototype.patch = function (newTree, context) {
        if (this.batchs.length) {
            this.batchs.length = 0;
        }
        var stack = makeInitialStackState(context, newTree, this.tree);
        var parent = null;
        while (stack.length) {
            var next = stack.pop();
            var newElement = next.newElement, oldElement = next.oldElement, context_2 = next.context, isKeyedItem = next.isKeyedItem;
            var difference = void 0;
            var currentRoot = next.root;
            if (!next.parsed) {
                _a = patchComponent(context_2, newElement, oldElement), context_2 = _a[0], newElement = _a[1], oldElement = _a[2];
                if (!newElement && !oldElement) {
                    continue;
                }
                if (newElement && oldElement) {
                    newElement._stem = oldElement._stem;
                }
                next.newElement = newElement;
                next.oldElement = oldElement;
                next.context = context_2;
                if (newElement && newElement._stem) {
                    currentRoot = next.newElement;
                }
                difference = difference_1.diff(oldElement, newElement);
                next.difference = difference;
                if (oldElement) {
                    util_1.invariant(!oldElement.dom, 'Dom element was accidentally removed.');
                }
                this.batchs.push({
                    root: currentRoot,
                    parent: parent ? parent.newElement : null,
                    newElement: newElement,
                    oldElement: oldElement,
                    isKeyedItem: isKeyedItem,
                    difference: difference,
                    context: next.context
                });
                next.newChildren = newElement ? newElement.children.slice() : [];
                next.oldChildren = oldElement ? oldElement.children.slice() : [];
                next.parsed = true;
            }
            if ((next.newChildren.length || next.oldChildren.length) &&
                (!next.difference ||
                    next.difference.flags === 0 ||
                    next.difference.flags === 8 /* REPLACE_ELEMENT */)) {
                stack.push(next);
                stack.push(createNextStackState(context_2, parent, next, oldElement));
                parent = next;
            }
        }
        var _a;
    };
    return FuelStem;
}());
exports.FuelStem = FuelStem;
