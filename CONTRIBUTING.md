Here are some quick notes on contributing to MLscript. (Written by Lionel, aka @LPTK.)

## Contribution Quality

The bar for contributing to this project is quite high.
If you're a student, you should be ready to put a lot more efforts and polishing into your changes
than you would for a course or personal project.
In fact, I expect a lot more polishing than would be expected for many other research projects.

### For Draft PRs

It is okay for draft PRs to contain work-in-progress changes that are not expected to be merged yet.
You can ask my opinion on your changes or on specific design considerations,
but you should not expect a full and detailed review from me if your PR is a draft.

### For Non-Drafy PRs

I am an extremely detail-oriented person,
and I will usually look at every single line of changed source code in your PR.
Therefore, **before you request a review from me**,
please make sure that **you have reviewed _the entire diff_ of your changes carefully**.
I should not have to put in more work than you in revieweing the diff
– if I end up doing so, it means you have somehow failed at your contribution job and you have wasted some of my time.
You should be able to explain and defend every single line of your changes.
In particular, please be mindful not to pollute your PR with random whitespace changes
and other leftovers from your local experimentations.

Ideally, I should be able to review your changes
by asking a few clarifying questions and making a few minor suggestions.
If some code is not clear enough to understand with a little bit of context,
it would be best to document the logic in the code using comments.

The way this is _not_ supposed to happen is that I have to keep coming back to your PR,
continually finding more problems and more unpolished or unclear changes,
and having to go through lots of back-and-forth interactions this way.
This will only lead to growing frustration on both ends.
Please be considerate of my time, which is often extremely scarce,
and make sure I never have to ask for a change or clarification more than once.

## Pull Request Etiquette

During the PR review process, we make use of GitHub comments to track suggestions
and clarification requests.
Resolving all comment threads is necessary for GitHub to allow the PR to be merged.

I realize it is not always clear to everyone when comment threads should be resolved, and by whom.
The general principles are the following:

 * If the comment is a change suggestion...
 
   * If it's clear and uncontroversial how to apply the suggestion,
     you should resolve the comment after you have made the corresponding changes to your code _and_ pushed that code to your branch.
   
   * If you are not 100% sure that you have applied the suggestion correctly,
     leave a comment asking me to have a look.
     DO NOT resolve the comment in this case.
   
   * If you don't fully understand or agree with the suggestion, reply to the comment with your questions and rebuttals.
     DO NOT resolve the comment in this case.
   
 * If the comment is a clarification request, answer it as best you can and wait for my feedback.
   DO NOT resolve the comment in this case.
   I will either come back with further questions or suggestions, or close the comment MYSELF if I find your answer satisfactory.

Essentially, a comment that I made must _either_ receive an answer from you (as a child comment) and left unresolved
_or_ be 100% addressed in your code and marked resolved (but only if you are sure about it; if not, leave a child comment and don't resolve the discussion).

The reason for these guidleines is mostly that GitHub's UI is poor and rather inappropriate.
In particular, I will not see a comment answer you make if you resolve the conversation,
because the UI will usually not show your response to me.  
(As a small digression, I think the UI would be better if _both_ the commenter _and_ the PR author would need to independently mark a comment as resolved
before the comment is considered truly resolved by GitHub and subsequently hidden.)
