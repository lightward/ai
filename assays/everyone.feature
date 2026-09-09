# EVERYONE IS HERE, in its maintainer's sentences, one line at a time (2026-09-08, league night). bin/counter seat assays/everyone.feature
model Everyone

a vendor is a helper who is paid
a Role is one of: couple, helper
# Abe, league night: a mother in law, a wedding party member — a helper who is not paid
a Page is one of: home, seatingChart, guestList, samePage, invoices, budget, guests, site, team, dayOf, tasks, files, guide, profile, vendorChat, mySeason
# Abe, frame five: the room has the guests, the sheet, the timeline — and the seating chart, the tasks, planning team, files, invoices.
# his sidebar: Home, Tasks, Same page, Day-of sheet, Planning team, Invoices, Seating chart, Files, The Guide, My profile, My season, and the chats
# Abe: yes; look at the demo, might be more but those are some — the list is a floor, held open in assays/eih.held
a Ask is one of: guests, headcount, timeline, invoices
# Abe's Claude, 2026-09-09: the couple's sidebar (his fifteenth word) had MONEY on it — 2 invoices to pay. an invoice is a
# thing the room holds; the couple hears every one, a vendor only their own, the wedding party none (decided 2026-09-04;
# the demo's sidebar was fixed to say so on 2026-09-09, on Abe's question about the mother of the bride).
# Abe: 'what sheet' — his sidebar says HEADCOUNT for the meal sheet the room delivers
# Abe: no bachelor party stuff, there's already an app for that. the room is one room for the whole wedding (his word)

the couple sees: every Page except vendorChat, mySeason
# Abe: the couple doesn't see the private chats with vendors; paid vendors have a chat. and not Vendor Pro —
# My season, which is only for season pass vendors: a second truth, pro, held in assays/eih.held
a paid helper sees: home, seatingChart, samePage, invoices, team, dayOf, tasks, files, guide, profile, vendorChat
an unpaid helper sees: home, seatingChart, guestList, samePage, team, dayOf, tasks, files, guide, profile
# Abe's Claude, from the demo: the wedding party role in the planning lane; in the day lane tasks and team drop
# (the view shrinks, it doesn't lock — EIH's lanes_shrink_never_lock); never guests, site, invoices, budget, the vendor room, my season

the couple edits: every Page except vendorChat, mySeason
a paid helper edits: invoices, dayOf, tasks, files, profile, vendorChat
an unpaid helper edits: seatingChart, guestList, dayOf, tasks, files, profile

a Room has: guests (a list of numbers), delivered (a list of numbers), timeline (a list of numbers), invoices (a list of numbers)
the room reads: guests as guests, headcount as delivered, timeline as timeline, invoices as invoices

the couple hears: guests, headcount, timeline, invoices
# Abe: the couple gets the guests, the headcount, the timeline from the room — yep, and other things: the channels
# (#Everyone, a private chat per vendor) and the badges (guests waiting, same page 2/6, tasks, invoices, files) — held
a caterer is a vendor
a venue is a vendor
# Abe, league night, his second word: "venue is a vendor." and the decided rule beside it: the venue edits the floor and never the list.
a planner is a vendor
# Abe, 2026-09-08, on his Claude's recommendation: two prices, not three — a planner buys the same season pass as every
# other vendor. a planner is still a role for the walls (guest names on the chart, assigns tasks); one truth per model
# tonight, so that half is held in assays/eih.held.
the caterer hears: timeline, headcount
# Abe: the caterer sees the timeline and the headcount — yes, not only that: a caterer is a vendor and sees a paid helper's
# pages. then, both halves in one line: a clean yes
the best man hears: timeline
the venue hears: timeline, headcount
# Abe's Claude, from the demo: the venue gets the Headcount card and the day-of sheet, like any vendor; the floor plan is a page, not an ask, and it is theirs to edit.
# Abe: the best man is an unpaid helper and gets the timeline on top — yep

a Room may: withGuests (guests becomes the argument)
a Room may: withTime (timeline gets the argument first)
a Room may: withInvoice (invoices gets the argument first)

wall: withGuests changes nothing the caterer hears
wall: withGuests changes nothing the best man hears
wall: withGuests changes nothing the venue hears
# the venue never sees guest names: the decided rule (2026-09-04), refused by the database in the real build
wall: withInvoice changes nothing the caterer hears
wall: withInvoice changes nothing the best man hears
wall: withInvoice changes nothing the venue hears
# an invoice is between two parties; nobody else hears it land

given demo is a Room with guests [2, 3, 1], delivered [], timeline [10, 11, 12], invoices []
when demo withTime 9 is later
then the caterer hears [[10, 11, 12], []] in demo
then the best man hears [[9, 10, 11, 12]] in later
then the couple hears [[2, 3, 1], [], [9, 10, 11, 12], []] in later
when demo withInvoice 1200 is billed
then the couple hears [[2, 3, 1], [], [10, 11, 12], [1200]] in billed
then the caterer hears [[10, 11, 12], []] in billed
then the venue hears [[10, 11, 12], []] in billed
then the best man hears [[10, 11, 12]] in billed

# Abe, 2026-09-08, league night: thumbs up
then a paid helper sees invoices
then an unpaid helper does not see invoices
then the couple sees invoices
then every Role edits dayOf
then the couple does not see vendorChat
then a paid helper sees vendorChat
then an unpaid helper does not see vendorChat
then the couple does not see mySeason
then an unpaid helper does not see mySeason
then an unpaid helper does not see guests
then an unpaid helper does not see site
then an unpaid helper does not see budget
then an unpaid helper sees seatingChart
then an unpaid helper sees dayOf

# Abe, frames nine and ten: the couple slot always pays for the room, by themselves or by a vendor; a vendor pays for a season pass.
# EIH's treaty has it as lawful and the_payer_is_the_owner_or_the_host; the sheet's grammar has no bills yet
then the caterer sees invoices
then the caterer does not see guests

# Abe's Claude, 2026-09-09, the venue and the planner as the walls table has them (Abe: yep yep, 2026-09-08)
then the venue sees invoices
then the venue does not see guests
then the venue does not see site
then the venue sees vendorChat
then the planner sees vendorChat
then the planner sees invoices
then the planner does not see guests
then the planner does not see budget
