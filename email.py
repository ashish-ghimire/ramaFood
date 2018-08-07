#!/usr/bin/env python3

import getpass, imaplib, email
import re
from itertools import tee, islice, chain  #, zip
import html2text
#The html2text parser aove was developed by Aaron Swartz.
# I got it from http://www.aaronsw.com/2002/html2text/
import parsedatetime
import pytz
from pytz import timezone
from datetime import datetime
import datefinder
from email.header import decode_header
import math

# For MongoDB
import pymongo
from pymongo import MongoClient
import configparser

def findSmallestNumber(someIteratable):
    smallestNumber = math.inf
    for i in someIteratable:
        if i < smallestNumber:
            smallestNumber = i

    return smallestNumber

def removeAllNewLinesExceptParagraphChanges(bodyText):
    newBody = ""
    # paragraphs = re.split(r'(\n|\t|\r){2,}(?=[A-Z])', bodyText)
    # The regex below splits a text based on paragraphs. Based on my data (Ramapo emails), paragraph
    # boundaries can be identified by 2 new lines followed by a capital letter
    # This does not always work but works in most cases.
    paragraphs = re.split( r'(\n|\t|\r){2,}(?=(\*)*[A-Z)])' , bodyText)
    newlines = ('\n', '\t', '\r')
    for oldParagraph in paragraphs:
        if oldParagraph == None or oldParagraph in newlines:
            continue

        newParagraph = oldParagraph.replace('\n', " ")
        newBody += (newParagraph + 2*"\n")

    return newBody

def scrapLinesWithImages(body):
    #Also remove everything inside [ ] brackets
    imageTypes = ['.jpg', '.jpeg', '.bmp', '.gif', '<', 'KB']
    #[inline image 1] is a familiar pattern I got when parsing email bodies. I want to get rid of that
    for i in imageTypes:
        if i in body:     # Do a case insensitive search
            return " "
    return body


def beautifyText(bodyText):
    lines = bodyText.split('\n') # Break up the paragraph into multiple lines.
                                 # Don't parse the first and the last line

    body = ''
    for i in lines:
        i = html2text.html2text(i)    # Remove html tags
        i = re.sub(r'^https?:\/\/.*[\r\n]*', '', i)       # Remove all links
        i = scrapLinesWithImages(i)
        i = re.sub( r'\[(\w|\W)+\]', '', i) #remove everything between [ ]
        body += i

    return body


def isThisAFreeEvent(body):
    dollarIndex = body.find('$')
    boundary = 30 #Check 30 characters to the right of "$" and 30 characters to the left of "$"
    if dollarIndex == -1:
        return True

    remainingChar = len(body) - dollarIndex
    if remainingChar < boundary:
        rightOfDollar = body[dollarIndex:]
    else:
        rightOfDollar = body[dollarIndex:dollarIndex + boundary]

    if dollarIndex > boundary:
        leftOfDollar = body[dollarIndex - boundary:dollarIndex]
    else:
        leftOfDollar = body[:dollarIndex]

    if re.search(r"gift([ -]){0,1}card", leftOfDollar, re.IGNORECASE) or re.search(r"gift([ -]){0,1}card", rightOfDollar, re.IGNORECASE):
        return True
    return False


# The function below is the most important function in this script and in the entire
# project beacause this function detects if an event contains food related information.
# Unsurprisingly, the function is computationally expensive.
def isThisAFoodEvent(par):
    #To Dos: Make foodKeywords case insensitive
    #       'will AROUND 7 food', 'enjoy AROUND 5 food'. Create expressions that help you with this.
    #        Can both things listed above be done using regEx?

    if not isThisAFreeEvent(par):
        return False

    foodKeywordPatterns = (
        r"Food will be", r'\brefreshment', r'and food',
        r"food and", r'\bdrinks\b', r'ice[- \.]cream',
        r'\bpizza\b', r'\bsandwich\b', r"\bmoe's\b",
        r"\bchipotle\b", r"\bmozzarella\b", r"\btaco\b",
        r"for food", r"\bbagel\b", r"\bpasta\b",
        r"\bnuggets\b", "\bchilli\b", "\bdumpling\b",
        "\bmomo\b", r"\bfajita\b", r"\bchicken\b",
        r"\bpork\b", r"\broast\b", r"\bcheese\b",
        r"enchilada", r"\bwings\b", r"\bpie\b",
        r"\bnachos\b", r"\bcookies\b", r"burger",
        r"\bturkey\b", r"will be served", r'cake\b',
        r'snack', r'\bdessert\b', r'\bdinner\b',
        r"nicky's", r"bbq", r'\bnoodles\b',
        r'\bhalal\b', r'\bkosher\b', r'fries', r'cuisine',
        r'jun lung', r'carnival\b',
        # r'(Indian|Chinese|Mexican|Korean|Italian|delicious|tasty|Italian|Latin|Spanish|Asian|Nepali|Brazilian) food',
        # The computationally expensive regEx above did not improve food detetion rate significantly

        # great food
        r"\bgreat\W+(?:\w+\W+){0,2}?food\b",

        r"ve\W+(?:\w+\W+){0,2}?food\b", #have food.  We've got food

        #mo:mo
        r"\bmo([:]){0,1}mo(s){0,1}\b", # Mo:mos are my favorite NEpali dish. So, I would be sad if my app doesn't detect events with free mo:mo

        # (free AROUND 2 food)
        r"\bfree\W+(?:\w+\W+){0,2}?food\b",

        # (be AROUND 6 food)
        r"\bbe\W+(?:\w+\W+){0,6}?food\b",

        # OR (food AROUND 4 from). Regex is below:
        r"\bfood\W+(?:\w+\W+){0,4}?from\b",

        # OR (of AROUND 2 food)
        r"\bof\W+(?:\w+\W+){0,2}?food\b",

        # OR (enjoy AROUND 5 food)
        r"\benjoy\W+(?:\w+\W+){0,5}?food\b"
    )

    for aPattern in foodKeywordPatterns:
        if re.search(aPattern, par, re.IGNORECASE):
            return True
    return False


# The function below removes standard signtatures from emails with food information
# This function does not detect signatures like "-John" because a hyphen does not always
# indicate that any text after the hypehn is a signature. Although signatures that simply
# include a sender's name is extremely common, the name can't be identified as a signature.
def removeSignature(body):
    signatureStartIndex = []

    # signatureFormats is based on top voted answer in
    # https://stackoverflow.com/questions/1372694/strip-signatures-and-replies-from-emails
    signatureFormats = (
                            '-----Original Message-----',
                            # "From: "         # (failsafe four Outlook and some other reply formats)
                            'Sent from my iPhone',
                            "Thank you,",
                            "Thanks,",
                            "Thank You,",
                            "Best,",
                            "Regards",
                            'Sincerely,',
                             60 * "=", #This signature character is unique to Ramapo
                            '505 Ramapo Valley Road',
                            '505 Ramapo Valley Rd',
                            "Forward email",
                            "Best wishes"
                        )

    for i in signatureFormats:
        index = body.find(i)        #This has to be a case insensitive search
        if index != -1:
            signatureStartIndex.append(index)

    regexSignaturePatterns = (
        r'On\W+(?:\w+\W+){11,15}?wrote',
        r'Fwd:\b',
        r"(\n| |\r|\*)--( ){0,1}(\n|\r)",
        # r"(\r| )--( ){0,1}\r",
        r'(\n|\r| )________________________________(\n|\r)'
    )

    for aPattern in regexSignaturePatterns:
        searched = re.search(aPattern, body)
        if searched != None:
            signatureStartIndex.append(searched.span()[0])

    if len(signatureStartIndex) > 0:
        smallestIndex = findSmallestNumber(signatureStartIndex)
        body = body[:smallestIndex-1]

    return body


#The function below was written by nosklo in stackoverflow at
#  https://stackoverflow.com/questions/1011938/python-previous-and-next-values-inside-a-loop#1012089
def previous_and_next(some_iterable):
    some_iterable = some_iterable.split() #I added this line to make the fucntion work according to my specifications
    prevs, items, nexts = tee(some_iterable, 3)
    prevs = chain([None], prevs)
    nexts = chain(islice(nexts, 1, None), [None])
    return zip(prevs, items, nexts)

def addCSIEvent(paragraph):
    #Get the date and time if possible. If time is not possible or getting time would be unusually slow, don't get time
    #As soon as you get the date for event, break
    #The event details is the paragraph itself
    months = ('January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December') #spell check?. What if Jan or Feb
    par = paragraph
    eventDate = ''
    event = dict()

    for previous, item, nxt in previous_and_next(paragraph):
        if item in months:
            eventDate = previous + ' '+ item + ' ' + nxt
            break

    if isThisAFoodEvent(par):
        eventDate = eventDate.replace("^", "") #Maybe do more? Remove anything other than th, nd, st and numbers
        event['eventDate'] = eventDate
        event['title'] = 'CSI Event'
        beautifulText = removeAllNewLinesExceptParagraphChanges(par)
        event['eventDetails'] = beautifulText
        listOfEvents.append(event)

# this function utilizes parsedatetime module's ability to recognize date related info
# from strings to parse event dates. Parsedatetime gave me too many false leads
# when I tried to parse date related info from an unprocessed text. So, I processed
# string for date related information myself and provided parsedatetime with a string that
# always has date realted info. parsedatetime parsed the final date and converted
# into appropriate function for processing
def convertToPythonDatetimeObj(aDate):
    c = parsedatetime.Constants()
    c.BirthdayEpoch = 80
    p = parsedatetime.Calendar(c)

    time_struct, parse_status = p.parse(aDate)
    return datetime(*time_struct[:6])

# The first of three possible iterations to find date
# Iteration 1 : tries to find date in "November 25, 2018", "OCt 5", etc. format
def dateIteration1(body):
    months = (
                'January', 'February', 'March', 'April', 'May', 'June', 'July',
                'August', 'September', 'October', 'November', 'December'
            ) #spell check?. What if Jan or Feb

    monthsAbbreviated = (
        'Jan', 'Feb', 'Mar', 'Apr', 'Jun', 'Aug', 'Sept', 'Sep', 'Oct', 'Nov', 'Dec',
        "Jan.", "Feb.", "Mar.", "Apr.", "Aug.", "Sept.", "Sep.", "Oct.", "Nov.", "Dec."
    )

    foundDate = False
    result = ''

    eventDate = ''

    for previous, item, nxt in previous_and_next(body):
        if item in months or item in monthsAbbreviated:
            #Find if the word next to month is a number, Don't want to extract sth like 'March madness'.
            # Also, take into accunt March 5th, Aug 1st....
            possibleDay = re.findall('\d+', nxt)  # Also, take into accunt March 5th, Aug 1st....
            if possibleDay:
                day = possibleDay[0]
                item = item.replace(".", "")
                eventDate = item + ' ' + day
                foundDate = True
                break     #Stops after you find first date. Is this always accurate though?

    if not (eventDate == ''):
        result = convertToPythonDatetimeObj(eventDate)

    return (foundDate, result)

# The second of three possible iterations to find date
# Iteration 2: tries to find date in "5-14" or 6/20/2018 (Based on US date form)
def dateIteration2(body):
    #EXplore using OR (|) and try to do all 3 types of regex searches in 1 line
    foundDate = False
    result = ''
    # Date iteration 2
    # Matching date formats
    # 3/27    \d{1,2}[\/]{1} {0,1}\d{1,2}
    # 5/2/2015    \d{1,2}[\/-]{1} {0,1}\d{1,2} {0,1}[\/-]{1}\d{2,4}
    # 2015-9-5    \d{4}[\/-]{1} {0,1}\d{1,2}[\/-]{1} {0,1}\d{0,1}
    date = re.search('\d{1,2}[\/]{1} {0,1}\d{1,2}', body)

    if date == None:
        date = re.search( "\d{1,2}[\/-]{1} {0,1}\d{1,2} {0,1}[\/-]{1}\d{2,4}" ,body)

        if date == None:
            date = re.search( "\d{4}[\/-]{1} {0,1}\d{1,2}[\/-]{1} {0,1}\d{0,1}" ,body)

    if date != None:
        result = convertToPythonDatetimeObj( date.group(0) )
        foundDate = True

    return (foundDate, result)

# The third of three possible iterations to find date
# Iteration 3: Finally, this iteration tries to find date in natural language
# format like "tonight", "tomorrow", "right now"
def dateIteration3(body):
    foundDate = False
    result = ''
    dateHumanLang = [
        'right now',
        'tonight',
        'today',
        'tomorrow'
    ]

    pattern = "(" + "|".join(dateHumanLang) + ")"
    date = re.search(pattern, body, re.IGNORECASE)
    if date != None:
        result = convertToPythonDatetimeObj( date.group(1) )
        foundDate = True
    else:
        date = re.search( 'now', body, re.IGNORECASE)   #This is last ditch effort to find dates. Don't want to include now
        #print('Date is', date)                          # in dateHumanLang because now may not necessarily denote event's date
        if date != None:
            result = convertToPythonDatetimeObj( date.group(0))
            foundDate = True

    return (foundDate, result)


# Parsing date from different format of emails was tricky especially because
# date parsing libraries like parsedatetime did not work as I expected them to work
# Since identifying eventDates is so critical, it was important for me to get
# it right in a way that's not too computationally expensive. The date parsing
# process goes through three iterations. The process continues to the next
# iteration if the previous iteration does not identify any dates. This is
# computationally cheaper than running all text through three iterations to parse
# date. Why go to the next step if you don't need to?
# Iteration 1 : tries to find date in "November 25, 2018", "OCt 5", etc. format
# Iteration 2: tries to find date in "5-14" or 6/20/2018 (Based on US date form)
# Iteration 3: Finally, this iteration tries to find date in natural language
# format like "tonight", "tomorrow", "right now"
def findEventDate(body):
    itr1Result = dateIteration1(body)
    if itr1Result[0]: #date found in first iteration
        return itr1Result[1]

    itr2Result = dateIteration2(body)
    if itr2Result[0]: #date found in first iteration
        return itr2Result[1]

    itr3Result = dateIteration3(body)
    return itr3Result[1]


# Daily Digest emails are sent out to every Ramapo College student almost everyday
# during Fall and Spring semesters. The type of emails that has decent amount of
# food avaibility information.
# To do: Make this function more scalable. At times, this function depends on
# email's characteristics that are only specific to Ramapo College
def addDailyDigestEvent(paragraph):
    #Get the date and time if possible. If time is not possible or getting time would be unusually slow, don't get time
    #As soon as you get the date for event, break
    #The event details is the paragraph itself minus the first line. The first line is title
    lines = paragraph.split('\n') #Break up the paragraph into multiple lines. Don't parse the first and the last line
    title = lines[1]
    #print("Title is : ", html2text.html2text(title) )

    body = ''
    for i in range(2, len(lines) -1):
        body += html2text.html2text(lines[i])

    event = dict()

    if isThisAFoodEvent(body):
        eventDate = findEventDate(body)
        if eventDate != '':
            event['eventDate'] = eventDate
            event['title'] = title
            beautifulText = removeAllNewLinesExceptParagraphChanges(body)
            event['eventDetails'] = beautifulText
            listOfEvents.append(event)


# Serially go through all text parts of an email. This function does not
# parse food avaibility information from images, html text and fancy stuff like
# that. However, the function can still parse food avaibility information from
# 99% emails that I choose to parse information from
def walk(msg, possibleListOfParas):
    plainTextCount = 0

    for part in msg.walk():
        try:
            if part.get_content_type() == "text/plain":
                body = part.get_payload(decode=True) #to control automatic email-style MIME decoding (e.g., Base64, uuencode, quoted-printable)
                body = body.decode()
                possibleListOfParas.append(body)

                plainTextCount += 1
                #print(body)
            elif part.get_content_type() == "text/html":
                continue
        except UnicodeDecodeError:
            continue

    # The walk above should go through 80% of emails. However, you need to repeat
    # the same walk but a little differently to go through around 19% of emails.
    # 1% emails have just pictures or annoyingly fancy texts. I am okay with
    # my program not parsing those emails.
    if plainTextCount == 0: #Need to parse this msg in a different way
        for part in msg.walk():
            try:
                body = part.get_payload(decode=True) #to control automatic email-style MIME decoding (e.g., Base64, uuencode, quoted-printable)
                if body != None:
                    body = body.decode()
                    possibleListOfParas.append(html2text.html2text(body))
            except UnicodeDecodeError:
                continue


#Based on CSI Weekend Edition for the past 20 months, Weekend Edition email has a familiar pattern
#The program breaks an email to paragraphs. Based on emails' pattern, the first 3 and the last 7 paragraphs are useless as
# they don't form the body of the email
def parseCSIWeekendEmails(msg, possibleListOfParas):
    walk(msg, possibleListOfParas)
    for i in possibleListOfParas:
        paragraph = re.split('\n(?=[A-Z])', i)

        for j in range(3, (len(paragraph) - 7)):   #Parse this part for date and event details
            addCSIEvent(paragraph[j])


#Based on Ramapo Daily Digest email for the past 20 months, Ramapo Digest email has a familiar pattern
#The program splits a complete email body based on a peculiar trait. Every event in Ramapo digest email in the past
#24 months is separated by 60 '-' characters. So, if you split the email body based on this trait, you can efficiently
#get individual email data. Is this approach scalable? No. But, in the present context, is this efficient? Yes
#Does it do the job? Yes.
def parseDailyDigestEmails(msg, possibleListOfParas):
    walk(msg, possibleListOfParas)
    splitCharacter = 60 * '-'
    for i in possibleListOfParas:
        paragraph = i.split(splitCharacter)

        # We can ignore the first two elements of a paragraph because they don't contain any data relevant for
        # food event parsing. Similarly, we can ignore the last element for the same reason
        for j in range(2, (len(paragraph) - 1)):   #Parse this part for date and event details
            addDailyDigestEvent(paragraph[j])


# Significant (around 35-40%) food availability information come from ramapo digest emails and
# CSI Weekend Edition emails. Residence halls and some clubs don't necessarily
# advertise their events on Ramapo Digest or on CSI Weekend emails. The function
# below identifies food avaibility info from these emails. These emails are tricky to parse
# because they don't have a standard format.
def addOtherEvents(body, emailSubject):
    title = html2text.html2text(emailSubject)
    event = dict()

    if isThisAFoodEvent(body):
        body = beautifyText(body)
        eventDate = findEventDate(body)
        if eventDate != '':
            event['eventDate'] = eventDate
            event['title'] = title
            beautifulText = removeAllNewLinesExceptParagraphChanges(body)
            event['eventDetails'] = beautifulText
            listOfEvents.append(event)
    # else:
    #     notAFoodEvent.append( beautifyText(body) )


def parseOtherEmails(msg, possibleListOfParas, emailSubject):
    walk(msg, possibleListOfParas)

    for i in possibleListOfParas:
        noSignatureBody = removeSignature(i)
        addOtherEvents(noSignatureBody, emailSubject)


# The connection string parameter comes from the config.json file in this
# particular example.
def connect_to_db(conn_str):
    global foodEventsTable
    client = MongoClient(conn_str)
    foodEventsTable = client.cmps364.foodEventsTable
    return client


def performDatabaseOperations():
    config = configparser.ConfigParser()
    pathWithDatabaseConnectionInfo = '/home/raa_tey/Documents/pythonEmail/config.ini'
    config.read(pathWithDatabaseConnectionInfo)
    connection_string = config['database']['mongo_connection']
    # This establishes the connection, conn will be used across the lifetime of the program.
    conn = connect_to_db(connection_string)

    for oneEvent in listOfEvents:
        document = {
            'title' : oneEvent['title'],
            'eventDate' : oneEvent['eventDate'],
            'eventDetails' : oneEvent['eventDetails']
        }
        foodEventsTable.insert_one(document)
    conn.close()


def performEmailOperations(emailAddress, password):
    M = imaplib.IMAP4_SSL('imap.gmail.com')
    M.login(emailAddress, password)
    M.select('dataOther') # This is the email folder / label you read emails
                            # I have set up my email filters such that emails
                            # with food availability info are automatically
                            # forwarded to a folder I want to download from.
                            # Folder's name is dataOther in this case
    typ, data = M.search(None, '(UNSEEN)')     # Adding 'UNSEEN' only reads unread emails

    # notAFoodEvent = []

    for num in data[0].split():
        typ, data = M.fetch(num, '(RFC822)')
        #print('Message %s\n%s\n' % (num, data[0][1]))
        msg = email.message_from_string(data[0][1].decode('utf-8'))
        subject = msg['Subject']
        if subject == None:
            subject = ''

        #subject = decode_header(msg['Subject'])
        #subject = str(msg['Subject'][0][0], 'utf-8')  #Convert byte object subject[0][0] to a decoded string object

        date_tuple = email.utils.parsedate_tz(msg['Date'])
        listTest = list()

        if 'digest@ramapo.edu' in msg['From']:
            parseDailyDigestEmails(msg, listTest)
        elif re.search(r'Weekend[^a-z]{2,4}Edition', subject):
            parseCSIWeekendEmails(msg, listTest)
        elif re.search(r'Public[^a-z]{2,4}Safety[^a-z]{2,4}Newsletter', subject):
            continue
        else:
            parseOtherEmails(msg, listTest, subject)

    M.close()
    M.logout()


config = configparser.ConfigParser()
pathWithDatabaseConnectionInfo = '/home/raa_tey/Documents/pythonEmail/config.ini'
config.read(pathWithDatabaseConnectionInfo)
emailAddress = config['gmailOperations']['emailAddress']
password = config['gmailOperations']['pw']


listOfEvents = list()
foodEventsTable = None  # This is the table in the MongoDB database in which
                        # food related information is stored

performEmailOperations(emailAddress, password)
performDatabaseOperations()
