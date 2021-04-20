extern int __VERIFIER_nondet_int(void);
extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }

/*
 * This source code is licensed under the GPLv3 license.
 *
 * Taken from Forester.
 */

#include <stdlib.h>

int main() {

	struct TreeNode {
		struct TreeNode* left;
		struct TreeNode* right;
	};

	struct TreeNode* root = malloc(sizeof(*root)), *n;
	root->left = NULL;
	root->right = NULL;

	while (__VERIFIER_nondet_int()) {
		n = root;
		while (n->left && n->right) {
			if (__VERIFIER_nondet_int())
				n = n->left;
			else
				n = n->right;
		}
		if (!n->left && __VERIFIER_nondet_int()) {
			n->left = malloc(sizeof(*n));
			n->left->left = NULL;
			n->left->right = NULL;
		}
		if (!n->right && __VERIFIER_nondet_int()) {
			n->right = malloc(sizeof(*n));
			n->right->left = NULL;
			n->right->right = NULL;
		}
	}

	n = NULL;

	struct TreeNode* pred;

	while (root) {
		pred = NULL;
		n = root;
		while (n->left || n->right) {
			pred = n;
			if (n->left)
				n = n->left;
			else
				n = n->right;
		}
		if (pred) {
			if (n == pred->left)
				pred->left = NULL;
			else
				pred->right = NULL;
		} else
			root = NULL;
		free(n);
	}

	return 0;

}
