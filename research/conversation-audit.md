# Conversation export coverage audit

The user's replacement `continue-planck-gap-analysis.md` is preserved unchanged.
The working-tree removal of the previous export is also left unstaged.

The previously downloaded share payload contains 694 message records including
tools and non-final material. Its text-user/final-assistant selection contains
17 user entries and 15 assistant replies; one user entry is the placeholder
“Original custom instructions no longer available”. Excluding that placeholder,
the replacement has the matching 16 User and 15 ChatGPT turn headings.

All 31 substantive message openings match lexical landmarks in the replacement.
Several endings differ because citation tokens are rendered differently; the
last assistant ending also differs. This is a coverage check, not a claim of
byte-identical or fully lossless conversion. No omitted substantive turn was
identified by this check. The former five-message archive was incomplete.

Reproduce against the existing downloaded payload:

```
node scripts/audit_conversation.cjs /tmp/newtonlean-chat-share.html continue-planck-gap-analysis.md
```

The temporary HTML is not a durable repository dependency. Re-download the
shared page if it is unavailable; the audit script parses data without executing
page scripts. No research claims are promoted from this conversation alone.
