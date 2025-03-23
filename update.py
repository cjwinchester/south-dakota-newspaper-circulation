from dataclasses import dataclass, field
import os
import json
import time
from pathlib import Path
from urllib.parse import urljoin, urlparse, parse_qsl
import random
import mimetypes
from datetime import datetime, date
import logging
import subprocess
from typing import Self
from string import Formatter
from email import utils

from playwright.sync_api import sync_playwright, Page
import requests
from bs4 import BeautifulSoup
import magic
from PIL import Image, ImageEnhance
from slugify import slugify
from internetarchive import get_item
from google import genai


logging.basicConfig(
    level=logging.INFO,
    format='{asctime} - {levelname} - {message}',
    style='{'
)

REQ_HEADERS = {
    'User-Agent': "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36"
}


def get_filesize_formatted(byte_count: int) -> str:
    """Formats byte count for humans.

    Args:
        byte_count (int): Number of bytes.

    Returns:
        byte_count_formatted (str): Byte count in a human-readable format.
    """

    byte_count_formatted  = ''

    if not byte_count:
        return byte_count_formatted

    for unit in ('', 'K', 'M', 'G', 'T'):
        if abs(byte_count) < 1024.0:
            byte_count_formatted = f'{byte_count:3.1f} {unit}B'
            return byte_count_formatted

        byte_count /= 1024.0

    return byte_count_formatted


def get_file_info(filepath: Path) -> dict:
    """Grabs basic metadata about a file.

    Args:
        filepath (Path): Local path to a file.

    Returns:
        file_info (dict): A dictionary with the keys "file_extension", "mimetype", "filesize_bytes" and "filesize_formatted".
    """

    if not isinstance(filepath, Path):
        filepath = Path(filepath)

    mimetype, _ = mimetypes.guess_type(
        filepath,
        strict=False
    )

    mimetype_inferred = magic.from_file(
        filepath,
        mime=True
    )

    mimetype = mimetype or mimetype_inferred

    if filepath.suffix:
        file_extension = filepath.suffix
    else:
        file_extension = mimetypes.guess_extension(
            mimetype,
            strict=False
        )

    filesize_bytes = filepath.stat().st_size
    filesize_formatted = get_filesize_formatted(filesize_bytes)

    file_info = {
        'file_extension': file_extension,
        'mimetype': mimetype,
        'filesize_bytes': filesize_bytes,
        'filesize_formatted': filesize_formatted
    }

    return file_info


@dataclass
class SdSosFiling:
    """ A filing from the South Dakota Secretary of State's
        old document-management system, with methods to
        download and process its constituent files into a
        finished PDF and gather some metadata along the way.

        Attributes:
            url (str): URL pointing to the filing's detail page.

            documentset_title (str): Title of the document set this filing belongs to.

            documentset_slug (str): Document set title slug.

            dir_tmp (Path): Local path to a temporary directory to store intermediate files. Defaults to Path('tmp').

            dir_pdfs (Path): Local path to a directory to store completed PDFs. Defaults to Path('pdfs').

            dir_thumbnails (Path): Local path to a directory to store thumbnails. Defaults to Path('thumbnails').

            keep_pdf (bool): Pass False if you want to delete the local copy of the PDF after it's uploaded to the Internet Archive. Defaults to True.

            thumbnail_height_px (int): Pixel height of thumbnail images. Defaults to 400.

            max_retries (int): Maximum number of retries to fetch intermediate files. Defaults to 30.

            req_headers (dict): Dictionary of headers to pass along with HTTP requests. Defaults to REQ_HEADERS.

            gemini_prompt_system (str): System prompt for the Gemini large language model. Defaults to an empty string.

            gemini_prompt_user (str): User prompt for the Gemini large language model. Defaults to an empty string.

            gemini_api_key (str): Gemini API key. Defaults to the `GEMINI_API_KEY` environment variable or an empty string if not present.

            gemini_model (str): Name of the Gemini model to use (https://ai.google.dev/gemini-api/docs/models). Defaults to 'gemini-2.0-flash-001'.

            filing_data (dict): A dictionary of data about the filing, scraped from its row in the search results table. Defaults to {}.

            fmt_str_pdf_metadata_title (str): A format string for the PDF metadata "title" attribute. Example: '{documentset_title} - {guid}'. Defaults to an empty string.

            fmt_str_pdf_metadata_description (str): A format string for the PDF metadata "description" attribute. Example: 'A {document_type} campaign finance filing submitted on {filing_date} by {candidate} - {guid}'. Defaults to an empty string.

            ia_access (str): Internet archive API key. Defaults to the `INTERNET_ARCHIVE_ACCESS_KEY` environment variable or an empty string if not present.

            ia_secret (str): Internet archive API secret. Defaults to the `INTERNET_ARCHIVE_SECRET_KEY` environment variable or an empty string if not present.
    """

    url: str
    documentset_title: str
    documentset_slug: str
    dir_tmp: Path = Path('tmp')
    dir_pdfs: Path = Path('pdfs')
    dir_thumbnails: Path = Path('thumbnails')
    keep_pdf: bool = True
    thumbnail_height_px: int = 400
    max_retries: int = 30
    req_headers: dict = field(default_factory=lambda: REQ_HEADERS)
    gemini_prompt_system: str = ''
    gemini_prompt_user: str = ''
    gemini_api_key: str = os.environ.get(
        'GEMINI_API_KEY', ''
    )
    gemini_model: str = 'gemini-2.0-flash-001'
    filing_data: dict = field(default_factory=dict)
    fmt_str_pdf_metadata_title: str = ''
    fmt_str_pdf_metadata_description: str = ''
    ia_access: str = os.environ.get(
        'INTERNET_ARCHIVE_ACCESS_KEY', ''
    )
    ia_secret: str = os.environ.get(
        'INTERNET_ARCHIVE_SECRET_KEY', ''
    )

    def __post_init__(self):
        """Sets additional attributes and creates directories"""

        for key in self.filing_data:
            setattr(self, key, self.filing_data[key])

        self.ia_identifier = f'{self.documentset_slug}-{self.guid}'

        self.ia_pdf_link = f'https://archive.org/download/{self.ia_identifier}/{self.guid}.pdf'

        self.filing_data.update({
            'internet_archive_identifier': self.ia_identifier,
            'url_internet_archive_pdf': self.ia_pdf_link
        })

        for d in [self.dir_tmp, self.dir_pdfs, self.dir_thumbnails]:
            d.mkdir(exist_ok=True)

        self.filepath_html = self.dir_tmp / f'{self.guid}.html'
        self.filepath_pdf = self.dir_pdfs / f'{self.guid}.pdf'
        self.filepath_thumbnail = self.dir_thumbnails / f'{self.guid}.gif'

        self._filepath_gemini_data = self.dir_tmp / f'{self.guid}-extracted-data.json'

    def download_and_parse_html(self) -> Self:
        """Download the filing's detail page and parse
           the HTML into a BeautifulSoup object.

            Returns:
                Self
        """

        if self.filepath_html.exists():
            with open(self.filepath_html, 'r') as infile:
                self.html = infile.read()
                self.soup = BeautifulSoup(self.html, 'html.parser')
            return self

        retries = self.max_retries
        url = self.url
        guid = self.guid
        req_headers = self.req_headers

        def attempt_download(retries=retries):
            """A recursive function that tries to download the HTML page.

            Args:
                retries (int): Number of attempts to download the file before throwing an exception.

            Raises:
                AssertionError, Exception
            """

            r = requests.get(
                url,
                headers=req_headers
            )

            r.raise_for_status()

            time.sleep(random.uniform(2, 4))

            try:
                assert 'document thumbnails' in r.text.lower()

                with open(self.filepath_html, 'w') as outfile:
                    outfile.write(r.text)

                logging.info(f'Wrote {self.filepath_html}')

                self.html = r.text
                self.soup = BeautifulSoup(r.text, 'html.parser')
                return self
            except AssertionError:
                time.sleep(random.uniform(2, 4))

                retries -= 1

                if retries == 0:
                    raise Exception(f'Could not retrieve page for {guid}')

                logging.warning(f'Failed to download {url}. Trying again ... ({retries})')

                attempt_download(
                    retries=retries
                )

        attempt_download()

        return self

    def download_and_process_images(self) -> Self:
        """Downloads the filing's separate images, boosts their
           sharpness and contrast and creates a thumbnail.

           Raises:
               Exception

           Returns:
               Self
        """
        if not self.html or not self.soup:
            self.download_and_parse_html()

        retries = self.max_retries
        guid = self.guid
        req_headers = self.req_headers
        detail_page_url = self.url

        filepath_images = []

        img_links = self.soup.find('table').find_all('a')
        img_links = [urljoin(self.url, x.get('href')) for x in img_links]

        def attempt_download(retries=retries):

            for url in img_links:

                qs = {x[0].split('?')[-1]: x[1] for x in parse_qsl(url)}

                image_number = qs.get('Image', '')

                filepath = self.dir_tmp / f'{guid}-{image_number}.jpg'

                if filepath.exists():
                    filepaths_images.append(filepath)
                    continue

                s = requests.Session()

                s.get(
                    detail_page_url,
                    headers=req_headers
                )

                time.sleep(random.uniform(2, 4))

                r = s.get(
                    url,
                    headers=req_headers
                )

                r.raise_for_status()

                time.sleep(random.uniform(2, 4))

                if 'text/html' in r.headers.get('content-type').lower():

                    retries -= 1

                    if retries == 0:
                        raise Exception(f'Could not download image at {url}')

                    logging.warning(f'Failed to download {url}. Trying again ... ({retries})')
                    
                    attempt_download(retries=retries)

                    continue

                with open(filepath, 'wb') as outfile:
                    outfile.write(r.content)

                logging.info(f'Downloaded {filepath}')

                filepath_images.append(filepath)

        attempt_download()

        filepath_images.sort()
        self.filepath_images = filepath_images

        images = [Image.open(f) for f in filepath_images]

        [ImageEnhance.Contrast(
            ImageEnhance.Sharpness(
                x
            ).enhance(50.0)
        ).enhance(50.0) for x in images]

        self.images = images

        if self.filepath_thumbnail.exists():
            return self

        # create a thumbnail
        size = self.thumbnail_height_px, self.thumbnail_height_px

        with Image.open(filepath_images[0]) as im:
            im.thumbnail(size)
            im.save(
                self.filepath_thumbnail
            )

        logging.info(f'Made a thumbnail: {self.filepath_thumbnail}')

        return self

    def build_pdf(self) -> Self:
        """Assemble the processed images into a PDF file, then
           call `ocrmypdf` to OCR the PDF and collect some file
           metadata.

           Raises:
               AssertionError

           Returns:
               Self
        """

        if not self.images:
            self.download_and_process_images()

        self.pages = len(self.images)
        self.filing_data['pages'] = self.pages

        if self.filepath_pdf.exists():
            file_info = get_file_info(self.filepath_pdf)

            self.filesize_bytes = file_info['filesize_bytes']
            self.filesize_formatted = file_info['filesize_formatted']

            self.filing_data['filesize_bytes'] = self.filesize_bytes
            self.filing_data['filesize_formatted'] = self.filesize_formatted
            return self

        # https://stackoverflow.com/a/22830468
        # assert that any variables in the PDF metadata format
        # strings are also attributes of this object
        fmt_variables_title = [fn for _, fn, _, _ in Formatter().parse(self.fmt_str_pdf_metadata_title) if fn is not None]

        fmt_variables_description = [fn for _, fn, _, _ in Formatter().parse(self.fmt_str_pdf_metadata_title) if fn is not None]

        assert not set(fmt_variables_description + fmt_variables_title).difference(set(self.__dict__.keys()))

        # build the title string
        fmt_dict_title = {x: getattr(self, x) for x in fmt_variables_title}
        pdf_title = self.fmt_str_pdf_metadata_title.format(**fmt_dict_title)

        # build the description string
        fmt_dict_description = {x: getattr(self, x) for x in fmt_variables_description}
        pdf_description = self.fmt_str_pdf_metadata_description.format(**fmt_dict_description)

        metadata = {}

        if pdf_title:
            self.pdf_title = pdf_title
            metadata['title'] = pdf_title

        if pdf_description:
            self.pdf_description = pdf_description
            metadata['subject'] = pdf_description

        self.images[0].save(
            self.filepath_pdf,
            'PDF',
            resolution=180.0,
            save_all=True,
            append_images=self.images[1:],
            **metadata
        )

        logging.info(f'Made a PDF: {self.filepath_pdf}')

        cmds = [
            'ocrmypdf',
            '--deskew',
            '--rotate-pages',
            '--clean',
            self.filepath_pdf,
            self.filepath_pdf,
        ]

        subprocess.run(cmds)

        file_info = get_file_info(self.filepath_pdf)
        self.filesize_bytes = file_info['filesize_bytes']
        self.filesize_formatted = file_info['filesize_formatted']

        self.filing_data['filesize_bytes'] = self.filesize_bytes
        self.filing_data['filesize_formatted'] = self.filesize_formatted

        return self

    def upload_pdf_to_ia(self) -> Self:
        """Upload PDF to the Internet Archive"""

        item = get_item(self.ia_identifier)

        metadata = self.filing_data.copy()

        r = item.upload(
            files=str(self.filepath_pdf),
            access_key=self.ia_access,
            secret_key=self.ia_secret,
            metadata=metadata,
            verbose=True,
            retries=50,
            retries_sleep=2
        )
        
        logging.info(f'Uploaded PDF to the Internet Archive: {self.ia_pdf_link}')

        return self

    def _gemini_extract_data(self) -> Self:
        """Uses the Gemini large language model to extract
           data from the PDF based on the prompts, then writes
           results to file.

           Returns:
               Self
        """
        if not self.pdf_filepath.exists():
            self.build_pdf()

        if self._gemini_data_filepath.exists():
            return self

        client = genai.Client(
            api_key=self.gemini_api_key
        )

        response = client.models.generate_content(
            model=self.gemini_model,
            config=types.GenerateContentConfig(
                temperature=0,
                system_instruction=self.gemini_prompt_system
            ),
            contents=[
                types.Part.from_bytes(
                    data=self.pdf_filepath.read_bytes(),
                    mime_type='application/pdf',
                ),
                self.gemini_prompt_user
            ]
        )

        self.extracted_data = response.text

        with open(self._gemini_data_filepath, 'w') as outfile:
            outfile.write(self.extracted_data)

        logging.info(f'Wrote {self._gemini_data_filepath}')

        return self

    def scrape(self, ia_upload: bool=False) -> Self:
        """Main function to scrape this filing."""

        self.download_and_parse_html()
        self.download_and_process_images()
        self.build_pdf()

        if ia_upload:
            self.upload_pdf_to_ia()

        return self

    def delete_tmp_files(self) -> Self:
        """Delete files in temporary directory."""

        files_to_delete = [
            self.filepath_html,
        ] + self.filepath_images

        if not self.keep_pdf:
            files_to_delete.append(self.filepath_pdf)

        for file in files_to_delete:
            file.unlink()
            logging.info(f'Deleted {file}')

        return self

    def __str__(self):
        return f'S.D. Secretary of State document - {self.documentset_title} - {self.guid}'


@dataclass
class SdSosDocumentSet:
    """An object to manage the extraction of documents
       and metadata from a document set stored in the
       South Dakota Secretary of State's old document-management system.

    Args:
        search_url (str): The URL of the document set's search page.

        title (str): The name of this document set.
        table_headers (list): A list of header values to use as column names in the search results.

        dir_pdfs (Path): Local path to a directory where completed PDFs will be stored. Defaults to Path('pdfs').

        dir_filings (Path): Local path to a directory to store intermediate files. Defaults to Path('filings').

        dir_data_file (Path): Local path to the directory where the metadata file will be created. Defaults to Path('.').

        max_retries (int): Number of times to retry loading the search results if an exception is thrown. Defaults to 10.

        post_processing_funcs (dict): A dictionary with zero or more table_header strings keyed to functions to process values of that type. Defaults to {}.

        fmt_str_pdf_metadata_title (str): A format string for the PDF metadata "title" attribute into which you can later interpolate variables. Example: '{documentset_title} - {guid}'. Defaults to an empty string.

        fmt_str_pdf_metadata_description (str): A format string for the PDF metadata "description" attribute into which you can later interpolate variables. Example: 'A {document_type} campaign finance filing submitted on {filing_date} by {candidate} - {guid}'. Defaults to an empty string.

        keep_pdfs (bool): Pass False if you want to delete the local copies of the PDFs after they're uploaded to the Internet Archive. Defaults to True.

        sort_columns (tuple): Columns by which to sort the JSON array before writing to file, in order. Defaults to ().
    """

    search_url: str
    title: str
    table_headers: list[str]
    dir_pdfs: Path = Path('pdfs')
    dir_data_file: Path = Path('.')
    max_retries: int = 10
    req_headers: dict = field(default_factory=lambda: REQ_HEADERS)
    post_processing_funcs: dict = field(default_factory=dict)
    fmt_str_pdf_metadata_title: str = ''
    fmt_str_pdf_metadata_description: str = ''
    keep_pdfs: bool = True
    sort_columns: tuple = ()

    def __post_init__(self):
        """Gets a list of completed guids, creates the slug,
           creates directories if needed, sets the data filepath,
           ensures post-processing keys are present in the
           table headers.

           Raises:
               Exception
        """

        for colname in self.post_processing_funcs:
            if colname not in self.table_headers:
                raise Exception(f'{colname} not in {self.table_headers}')

        self.slug = slugify(self.title, to_lower=True)

        self.dir_pdfs.mkdir(exist_ok=True)
        self.dir_data_file.mkdir(exist_ok=True)

        self.filepath_data = self.dir_data_file / f'{self.slug}-filings.json'

        current_data, completed_guids = [], []

        if self.filepath_data.exists():
            with open(self.filepath_data, 'r') as infile:
                data = json.load(infile)
                current_data = data
                completed_guids = [x['guid'] for x in data]

        self.current_data = current_data
        self.completed_guids = completed_guids

        # get/set a list of identifiers for filings that
        # already were uploaded to the Internet archive
        self.get_current_ia_identifiers()

    def get_search_results(self) -> Self:
        """Launch a Playwright browser to load the search
           results and parse the table HTML.

           Sets:
               self.search_results: A list of dictionaries with some basic metadata on each filing returned in the search results.

           Raises:
               AssertionError

           Returns:
               Self
        """
        try:
            with sync_playwright() as p:
                browser = p.firefox.launch(headless=False)
                context = browser.new_context()

                page = context.new_page()

                page.goto(
                    self.search_url,
                    timeout=0
                )

                time.sleep(random.uniform(5, 7))

                page.locator(f'input#cmdSubmit').click()

                table = page.locator('span#lbl_SearchInfo > table')

                time.sleep(random.uniform(5, 7))

                self.soup = BeautifulSoup(
                    table.inner_html(),
                    'html.parser'
                )

                browser.close()

            rows = self.soup.find_all('tr')
            self.search_results = []

            # loop over the table rows, skipping the headers
            for row in rows[1:]:
                cells = row.find_all('td')

                # throw if the header count doesn't match the
                # td count
                assert len(self.table_headers) == len(cells)

                row_data = dict(zip(
                    self.table_headers,
                    [x.text.strip() for x in cells]
                ))

                # find the link to the detail page
                url_partial = row.find('a').get('href')

                # grab fully qualified detail page URL
                row_data['source_url'] = urljoin(
                    self.search_url,
                    url_partial
                )

                # grab the doc guid
                row_data['guid'] = {x[0].split('?')[-1]: x[1] for x in parse_qsl(row_data['source_url'])}['DocGuid']

                # apply any post-processing functions
                for colname in self.post_processing_funcs:
                    func = self.post_processing_funcs[colname]
                    row_data[colname] = func(row_data[colname])

                self.search_results.append(row_data)
        except:
            time.sleep(random.uniform(4, 6))
            self.get_latest()

        return self

    def fetch_documents(self) -> Self:
        """Loops over the table of search results and
           creates an SdSosFiling object for each, then
           scrapes filing data and writes to file.

           Return:
              Self
        """
        if not self.search_results:
            self.get_search_results()

        self.new_filings = []

        for filing in self.search_results:
            guid = filing.get('guid')

            url = filing.get('source_url')

            filing_object = SdSosFiling(
                url,
                self.title,
                self.slug,
                keep_pdf=self.keep_pdfs,
                filing_data=filing,
                fmt_str_pdf_metadata_title=self.fmt_str_pdf_metadata_title,
                fmt_str_pdf_metadata_description=self.fmt_str_pdf_metadata_description
            )

            # is this filing already on the Internet Archive?
            ia_file_uploaded_already = filing_object.ia_identifier in self.current_ia_identifiers

            if guid in self.completed_guids and ia_file_uploaded_already:
                continue

            filing_object.scrape(
                ia_upload=not ia_file_uploaded_already
            )

            # add filing data to running list
            self.current_data.append(
                filing_object.filing_data
            )

            # dump to file to save state
            with open(self.filepath_data, 'w') as outfile:
                json.dump(self.current_data, outfile)

            self.new_filings.append(filing_object)

            filing_object.delete_tmp_files()

        # finally, sort the data and write the file out again
        if self.sort_columns:
            self.current_data.sort(
                key=lambda x: [x[col] for col in self.sort_columns]
            )

        with open(self.filepath_data, 'w') as outfile:
            json.dump(self.current_data, outfile)

        logging.info(f'Wrote {self.filepath_data}')

        return self

    def get_current_ia_identifiers(self) -> Self:
        """Fetch a list of identifiers for filings already
           uploaded to the Internet archive.
        """

        url = 'https://archive.org/advancedsearch.php'

        params = {
            'q': self.slug,
            'fl[]': 'identifier',
            'rows': len(self.current_data)+1,
            'output': 'json'
        }

        r = requests.get(
            url,
            headers=self.req_headers,
            params=params
        )

        if not r.ok:
            time.sleep(2, 4)
            self.get_current_ia_identifiers()

        self.current_ia_identifiers = [x['identifier'] for x in r.json()['response']['docs']]

        return self

    def __str__(self):
        return f'S.D. SOS document set: {self.title}'


def build_readme(
    filepath_in:Path,
    filepath_out: Path,
    replacements: dict={}
) -> Path:
    """Build the README.md file"""

    with open(filepath_in, 'r') as infile:
        tmpl = infile.read()

    for pair in replacements.items():
        tmpl = tmpl.replace(*pair)

    with open(filepath_out, 'w') as outfile:
        outfile.write(tmpl)

    logging.info(f'Wrote {filepath_out}')

    return filepath_out

def build_rss(
    filepath_in: Path,
    filepath_out: Path,
    items: list=[]
) -> Path:
    """Build an RSS feed."""

    if not items:
        return

    with open(filepath_in, 'r') as infile:
        tmpl = infile.read()

    rpl = (
        ('{% BUILD_DATE %}', utils.format_datetime(
            datetime.now()
        )),
        ('{% ITEMS %}', ''.join(items))
    )

    for pair in repl:
        tmpl = tmpl.replace(*pair)

    with open(filepath_out, 'w') as outfile:
        outfile.write(tmpl)

    logging.info(f'Wrote {filepath_out}')

    return filepath_out


if __name__ == '__main__':

    search_url = 'https://sdsos.gov/general-information/miscellaneous-forms/search/'

    documentset_title = 'South Dakota newspaper circulation'

    document_set = SdSosDocumentSet(
        search_url,
        documentset_title,
        table_headers=[
            'newspaper',
            'year'
        ],
        fmt_str_pdf_metadata_title='{documentset_title} - {newspaper} - {year} - {guid}',
        fmt_str_pdf_metadata_description='An ownership and circulation statement filed by South Dakota newspaper {newspaper} in {year}.',
        sort_columns=('year', 'newspaper')
    )

    document_set.get_search_results()
    document_set.fetch_documents()

    rss_items = []

    for filing in document_set.new_filings:
        pubdate = utils.format_datetime(
            date(int(filing.year), 1, 1)
        )

        item_str = f'''
        <item>
          <title>New filing - {filing.pdf_title}</title>
          <link>{filing.source_url}</link>
          <description>{filing.pdf_description}</description>
          <pubDate>{pubdate}</pubDate>
          <guid isPermaLink="false">{filing.guid}</guid>
        </item>
        '''

        rss_items.append(item_str)

    if rss_items:
        build_rss(
            'readme.template',
            f'{document_set.slug}-filings.xml',
            items=rss_items
        )

    years = [int(x['year']) for x in document_set.current_data]

    report_total = len(document_set.current_data)

    build_readme(
        'readme.template',
        'README.md',
        {
            '{% TOTAL_REPORTS %}': f'{report_total:,}',
            '{% EARLIEST_YEAR %}': str(min(years)),
            '{% LATEST_YEAR %}': str(max(years)),
            '{% UPDATED_DATE %}': datetime.now().strftime('%B %d, %Y')
        }
    )
