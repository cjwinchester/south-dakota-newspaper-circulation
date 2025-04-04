# South Dakota newspaper ownership and circulation statements

Improving access to [newspaper ownership and circulation statements](https://sdsos.gov/general-information/miscellaneous-forms/newspaper-ownership-circulation-statment.aspx) filed with the South Dakota Secretary of State.
- **Filings processed**: 3,422
- **Coverage**: 1999 - 2024
- **Updated**: March 23, 2025

[Subscribe to RSS feed](https://raw.githubusercontent.com/cjwinchester/south-dakota-newspaper-circulation/refs/heads/main/south-dakota-newspaper-circulation-filings.xml)

### Overview
[South Dakota Codified Law 17-2-2.5](https://sdlegislature.gov/Statutes/17-2-2.5) requires that newspapers each year "submit to the secretary of state ... a sworn statement of ownership and total print and online circulation for the previous calendar year, on forms prescribed by the secretary of state."

These filings are [collected on the Secretary of State's older document-management website](https://sdsos.gov/general-information/miscellaneous-forms/search), which serves filings as individually scanned pages at separate URLs (sometimes successfully). This makes research ... kind of difficult!

This project aims to fix that, using some Python to:
- Download the images for each filing (using [`Playwright`](https://playwright.dev/python/), [`requests`](https://requests.readthedocs.io/en/latest/) and [`BeautifulSoup`](https://www.crummy.com/software/BeautifulSoup/bs4/doc/))
- Optimize the images and assemble them into a single PDF with new metadata fields (using [`Pillow`](https://pillow.readthedocs.io/en/stable/index.html))
- Add an OCR layer to each PDF (using [`ocrmypdf`](https://ocrmypdf.readthedocs.io/en/latest/index.html))
- Mirror the PDF on the Internet Archive for easier/alternate retrieval (using [`internetarchive`](https://archive.org/developers/internetarchive/))

Along the way, we're also generating [thumbnail images](thumbnails) and gathering basic metadata about these public records in [`south-dakota-newspaper-circulation-filings.json`](south-dakota-newspaper-circulation-filings.json).

Stretch goals:
- [ ] Use a large language model to extract structured data from each report
- [ ] Build a crosswalk file to uniquely identify newspapers across time
- [ ] Build a basic search page

### Process
All the action happens in [`update.py`](update.py) with an instance of the class `SdSosDocumentSet`.

A Playwright browser loads the search page and performs a blank search, which generates a table of results. Various files related to each filing are downloaded into a temporary folder (`tmp`) and named after its unique identifier in the system (`guid`).

Specifically, for each row in the search results table, the script:
- Downloads the HTML behind the filing's detail page
- Parses the HTML file to look for image links and downloads them
- Sharpens and clarifies the images and assembles them into a single PDF with new metadata fields in `pdfs/{guid}.pdf`, then OCRs the PDF
- Generates a thumbnail in `thumbnails/{guid}.pdf`
- Conditionally uploads the PDF to the Internet Archive

Once the PDFs are generated, the script compiles data from individual filings into an array --

```json
[
    {
        "newspaper": "Yankton Daily Press & Dakotan",
        "year": 2024,
        "source_url": "https://sdsos.gov/general-information/miscellaneous-forms/search/Document.aspx?CabId=523E2A2A&DocGuid=20241205-0033-3100-5491-06c206dea21e", "guid": "20241205-0033-3100-5491-06c206dea21e", 
        "internet_archive_identifier": "south-dakota-newspaper-circulation-20241205-0033-3100-5491-06c206dea21e", 
        "url_internet_archive_pdf": "https://archive.org/download/south-dakota-newspaper-circulation-20241205-0033-3100-5491-06c206dea21e/20241205-0033-3100-5491-06c206dea21e.pdf",
        "pages": 2, 
        "filesize_bytes": 537674,
        "filesize_formatted": "525.1 KB"
    }
]
```

-- and writes it to [`south-dakota-newspaper-circulation-filings.json`](south-dakota-newspaper-circulation-filings.json).

### RSS feed
New filings are flagged in [`south-dakota-newspaper-circulation-filings.xml`](south-dakota-newspaper-circulation-filings.xml).