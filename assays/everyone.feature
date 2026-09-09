# EVERYONE IS HERE, in its maintainer's sentences, one line at a time (2026-09-08, league night). bin/counter seat assays/everyone.feature
model Everyone

a vendor is a helper who is paid
a Role is one of: couple, helper
# Abe, league night: a mother in law, a wedding party member — a helper who is not paid
a Page is one of: home, seatingChart, guestList, samePage, invoices, budget, guests, site, team, dayOf, tasks, files, guide, profile, vendorChat, mySeason
# Abe, frame five: the room has the guests, the sheet, the timeline — and the seating chart, the tasks, planning team, files, invoices.
# his sidebar: Home, Tasks, Same page, Day-of sheet, Planning team, Invoices, Seating chart, Files, The Guide, My profile, My season, and the chats
# Abe: yes; look at the demo, might be more but those are some — the list is a floor, held open in assays/eih.held
a Ask is one of: guests, sheet, timeline
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

a Room has: guests (a list of numbers), delivered (a list of numbers), timeline (a list of numbers)
the room reads: guests as guests, sheet as delivered, timeline as timeline

the couple hears: guests, sheet, timeline
the caterer hears: timeline, sheet
the best man hears: timeline

a Room may: withGuests (guests becomes the argument)
a Room may: withTime (timeline gets the argument first)

wall: withGuests changes nothing the caterer hears
wall: withGuests changes nothing the best man hears

given demo is a Room with guests [2, 3, 1], delivered [], timeline [10, 11, 12]
when demo withTime 9 is later
then the caterer hears [[10, 11, 12], []] in demo
then the best man hears [[9, 10, 11, 12]] in later
then the couple hears [[2, 3, 1], [], [9, 10, 11, 12]] in later

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
